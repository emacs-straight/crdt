;;; crdt.el --- Collaborative editing using Conflict-free Replicated Data Types  -*- lexical-binding: t; -*-

;; Copyright (C) 2021 Free Software Foundation, Inc.

;; Author: Qiantan Hong <qhong@alum.mit.edu>
;; Maintainer: Qiantan Hong <qhong@alum.mit.edu>
;; URL: https://code.librehq.com/qhong/crdt.el
;; Keywords: collaboration crdt
;; Version: 0.3.2

;; This file is part of GNU Emacs.

;; GNU Emacs is free software: you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or
;; (at your option) any later version.

;; GNU Emacs is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with GNU Emacs.  If not, see <https://www.gnu.org/licenses/>.

;;; Commentary:
;; This package provides a collaborative editing environment for Emacs.

;;; Code:

;;; Customs

(require 'xdg nil t)
(require 'cl-lib)
(require 'url)
(require 'color)
(require 'forms)
(require 'nadvice)
(require 'gnutls)

(defconst crdt-version "0.3.2")
(defconst crdt-protocol-version "0.3.0")

(defun crdt-version (&optional message)
  "Show the crdt.el version."
  (interactive (list t))
  (if message
      (message "crdt.el version %s" crdt-version)
    crdt-version))

(defgroup crdt nil
  "Collaborative editing using Conflict-free Replicated Data Types."
  :prefix "crdt-"
  :group 'applications)

(defcustom crdt-default-name (user-full-name)
  "Default display name."
  :type 'string)

(defcustom crdt-confirm-disconnect t
  "Ask for confirmation when a CRDT server is to stop the connection from some client."
  :type 'boolean)

(defvar crdt--log-network-traffic nil
  "Debug switch to log network traffic to *Messages*.")

(defvar crdt--inhibit-recover nil
  "Debug switch to disable error recovery mechanism.
This includes `crdt--with-recover' and `crdt--with-should-not-error'.")

(defcustom crdt-tuntox-executable "tuntox"
  "Path to the tuntox binary."
  :type 'file)

(defcustom crdt-tuntox-key-path (if (featurep 'xdg) (xdg-data-home) "~/")
  "Path to save tuntox's private key."
  :type 'directory)

(defcustom crdt-use-tuntox nil
  "Start tuntox proxy for CRDT servers."
  :type '(choice boolean (const confirm)))

(defcustom crdt-stunnel-executable "stunnel"
  "Path to the stunnel binary."
  :type 'file)

(defcustom crdt-tls-certificate
  (locate-user-emacs-file "crdt-tls.pem")
  "Path to TLS certificate file used for TLS-secured server."
  :type 'file)

(defcustom crdt-tls-private-key
  (locate-user-emacs-file "crdt-tls.pem")
  "Path to TLS private key file used for TLS-secured server."
  :type 'file)

(defcustom crdt-use-stunnel nil
  "Start stunnel proxy for CRDT servers."
  :type '(choice boolean (const confirm)))

(defcustom crdt-default-tls nil
  "Connecting with TLS (eins) protocol by default."
  :type 'boolean)

(defcustom crdt-read-settings-help-string
  (concat "\\[forms-next-field]:Next Field, \\[forms-prev-field]:Prev Field\n"
          "\\[forms-next-record]:History Next, \\[forms-prev-record]:History Prev\n"
          "\\[exit-recursive-edit]:OK, \\[abort-recursive-edit]:Cancel\n")
  "Help string for `crdt-read-settings'."
  :type 'string)

(defcustom crdt-default-session-permissions
  '(crdt-write-access-fcaps
    crdt-create-buffer-fcaps
    crdt-comint-fcaps
    crdt-xscheme-fcaps
    crdt-xref-fcaps)
  "A list that describes default policies for public session-scoped functions.
See `crdt-new-session'.'"
  :type '(list (or function symbol)))

(defcustom crdt-override-command t
  "Override local commands with corresponding remote commands when available."
  :type 'boolean)

(defcustom crdt-region-alpha 0.2
  "Alpha value for highlighting selections."
  :type 'float)

(defcustom crdt-tuntox-password-in-url nil
  "Whether or not to include the session password in the tuntox connection URL.
Useful if you plan to share your session URL over a trusted secure channel. Your
password will be in plaintext in the URL, so take care when sharing URLs with
this option enabled."
  :type 'boolean)

;;; Pseudo cursor/region utils

(defvar crdt-cursor-colors
  (let ((n 10))
    (cl-loop for i below n
          for hue by (/ 1.0 n)
          collect (color-hsl-to-rgb hue 0.5 0.5)))
  "List of candidate cursor colors.")

(defun crdt--get-cursor-color (user-id)
  "Get cursor color for USER-ID."
  (apply #'color-rgb-to-hex
         (nth (mod user-id (length crdt-cursor-colors)) crdt-cursor-colors)))

(defun crdt--get-region-color (user-id)
  "Get region color for USER-ID."
  (let ((background-rgb (color-name-to-rgb (face-attribute 'default :background))))
    (if background-rgb
        (apply #'color-rgb-to-hex
               (cl-mapcar
                (lambda (a b) (+ (* a crdt-region-alpha) (* b (- 1.0 crdt-region-alpha))))
                (nth (mod user-id (length crdt-cursor-colors)) crdt-cursor-colors)
                background-rgb))
      (crdt--get-cursor-color user-id))))

(defun crdt--move-cursor (ov pos)
  "Move pseudo cursor overlay OV to POS."
  ;; Hax!
  (let* ((eof (eq pos (point-max)))
         (end (if eof pos (1+ pos)))
         (display-string
          (when eof
            (unless (or (eq (point) (point-max))
                        (cl-some (lambda (ov)
                                   (and (eq (overlay-get ov 'category) 'crdt-pseudo-cursor)
                                        (overlay-get ov 'before-string)))
                                 (overlays-in (point-max) (point-max))))
              (propertize " " 'face (overlay-get ov 'face))))))
    (move-overlay ov pos end)
    (overlay-put ov 'before-string display-string)))

(defun crdt--move-region (ov pos mark)
  "Move pseudo marked region overlay OV to mark between POS and MARK."
  (move-overlay ov (min pos mark) (max pos mark)))

;;; CRDT ID utils
;; CRDT IDs are represented by unibyte strings (for efficient comparison)
;; Every two bytes represent a big endian encoded integer
;; For base IDs, last two bytes are always representing site ID
;; Stored strings are BASE-ID:OFFSETs. So the last two bytes represent offset,
;; and second last two bytes represent site ID
(defconst crdt--max-value (lsh 1 16))
;; (defconst crdt--max-value 16)
;; for debug
(defconst crdt--low-byte-mask 255)

(defsubst crdt--get-two-bytes (string index)
  "Get the big-endian encoded integer from STRING starting from INDEX.
INDEX is counted by bytes."
  (logior (lsh (elt string index) 8)
          (elt string (1+ index))))

(defsubst crdt--get-two-bytes-with-offset (string offset index default)
  "Helper function for CRDT--GENERATE-ID.
Get the big-endian encoded integer from STRING starting from INDEX,
but with last two-bytes of STRING (the offset portion) replaced by OFFSET,
and padded infintely by DEFAULT to the right."
  (cond ((= index (- (string-bytes string) 2))
         offset)
        ((< (1+ index) (string-bytes string))
         (logior (lsh (elt string index) 8)
                 (elt string (1+ index))))
        (t default)))

(defsubst crdt--id-offset (id)
  "Get the literal offset integer from ID.
Note that it might deviate from real offset for a character
in the middle of a block."
  (crdt--get-two-bytes id (- (string-bytes id) 2)))

(defsubst crdt--set-id-offset (id offset)
  "Set the OFFSET portion of ID destructively."
  (let ((length (string-bytes id)))
    (aset id (- length 2) (lsh offset -8))
    (aset id (- length 1) (logand offset crdt--low-byte-mask))))

(defsubst crdt--id-replace-offset (id offset)
  "Create and return a new id string by replacing the OFFSET portion from ID."
  (let ((new-id (substring id)))
    (crdt--set-id-offset new-id offset)
    new-id))

(defsubst crdt--id-site (id)
  "Get the site id from ID."
  (crdt--get-two-bytes id (- (string-bytes id) 4)))

(defsubst crdt--generate-id (low-id low-offset high-id high-offset site-id)
  "Generate a new ID between LOW-ID and HIGH-ID.
The generating site is marked as SITE-ID.
Offset parts of LOW-ID and HIGH-ID are overriden by LOW-OFFSET
and HIGH-OFFSET.  (to save two copying from using CRDT--ID-REPLACE-OFFSET)"
  (let* ((l (crdt--get-two-bytes-with-offset low-id low-offset 0 0))
         (h (crdt--get-two-bytes-with-offset high-id high-offset 0 crdt--max-value))
         (bytes (cl-loop for pos from 2 by 2
                      while (< (- h l) 2)
                      append (list (lsh l -8)
                                   (logand l crdt--low-byte-mask))
                      do (setq l (crdt--get-two-bytes-with-offset low-id low-offset pos 0))
                      do (setq h (crdt--get-two-bytes-with-offset high-id high-offset pos crdt--max-value))))
         (m (+ l 1 (random (- h l 1)))))
    (apply #'unibyte-string
           (append bytes (list (lsh m -8)
                               (logand m crdt--low-byte-mask)
                               (lsh site-id -8)
                               (logand site-id crdt--low-byte-mask)
                               0
                               0)))))

;; CRDT-ID text property actually stores a cons of (ID-STRING . END-OF-BLOCK-P)
(defsubst crdt--get-crdt-id-pair (pos &optional obj)
  "Get the (CRDT-ID . END-OF-BLOCK-P) pair at POS in OBJ."
  (get-text-property pos 'crdt-id obj))

(defsubst crdt--get-starting-id (pos &optional obj)
  "Get the CRDT-ID object at POS in OBJ."
  (car (crdt--get-crdt-id-pair pos obj)))

(defsubst crdt--end-of-block-p (pos &optional obj)
  "Get the END-OF-BLOCK-P at POS in OBJ."
  (cdr (crdt--get-crdt-id-pair pos obj)))

(defsubst crdt--get-starting-id-maybe (pos &optional obj limit)
  "Get the CRDT-ID at POS in OBJ if POS is no smaller than LIMIT.
Return NIL otherwise."
  (unless (< pos (or limit (point-min)))
    (car (get-text-property pos 'crdt-id obj))))

(defsubst crdt--get-id-offset (starting-id pos &optional obj limit)
  "Get the real offset integer for a character at POS.
Assume the stored literal ID is STARTING-ID."
  (let* ((start-pos (previous-single-property-change (1+ pos) 'crdt-id obj (or limit (point-min)))))
    (+ (- pos start-pos) (crdt--id-offset starting-id))))

;;; CRDT ID and text property utils

(defsubst crdt--get-id (pos &optional obj left-limit right-limit)
  "Get the real CRDT ID at POS in OBJ.
The search for start and end of CRDT ID block is limited by LEFT-LIMIT and RIGHT-LIMIT."
  (let ((right-limit (or right-limit (point-max)))
        (left-limit (or left-limit (point-min))))
    (cond ((>= pos right-limit) "")
          ((< pos left-limit) nil)
          (t
           (let* ((starting-id (crdt--get-starting-id pos obj))
                  (left-offset (crdt--get-id-offset starting-id pos obj left-limit)))
             (crdt--id-replace-offset starting-id left-offset))))))

(defsubst crdt--set-id (pos id &optional end-of-block-p obj limit)
  "Set the crdt ID and END-OF-BLOCK-P at POS in OBJ.
Any characters after POS but before LIMIT that used to
have the same (CRDT-ID . END-OF-BLOCK-P) pair are also updated
with ID and END-OF-BLOCK-P."
  (put-text-property pos (next-single-property-change pos 'crdt-id obj (or limit (point-max))) 'crdt-id (cons id end-of-block-p) obj))

(cl-defmacro crdt--with-insertion-information
    ((beg end &optional beg-obj end-obj beg-limit end-limit) &body body)
  "Setup some useful variables relevant to an insertion and evaluate BODY.
The insert happens between BEG in BEG-OBJ and END in END-OBJ,
if BEG-OBJ or END-OBJ is NIL, it is treated as current buffer.
The search for start and end of CRDT ID block is limited by BEG-LIMIT and END-LIMIT."
  (declare (indent 1) (debug ([&rest form] body)))
  `(let* ((not-begin (> ,beg ,(or beg-limit '(point-min)))) ; if it's nil, we're at the beginning of buffer
          (left-pos (1- ,beg))
          (starting-id-pair (when not-begin (crdt--get-crdt-id-pair left-pos ,beg-obj)))
          (starting-id (if not-begin (car starting-id-pair) ""))
          (left-offset (if not-begin (crdt--get-id-offset starting-id left-pos ,beg-obj ,beg-limit) 0))
          (not-end (< ,end ,(or end-limit '(point-max))))
          ;; (beg ,beg) ; it happens that no function relies on this particular binding
          (end ,end)
          (beg-obj ,beg-obj)
          (end-obj ,end-obj)
          ;; (beg-limit ,beg-limit) ; it happens that no function uses it right now.
          (end-limit ,end-limit))
     ,@body))

(defmacro crdt--split-maybe ()
  "Split the block if current insertion lies in some CRDT ID block.
Must be used inside CRDT--WITH-INSERTION-INFORMATION."
  '(when (and not-end (eq starting-id (crdt--get-starting-id end end-obj)))
    ;; need to split id block
    (crdt--set-id end (crdt--id-replace-offset starting-id (1+ left-offset))
     (crdt--end-of-block-p left-pos beg-obj) end-obj end-limit)
    (rplacd (get-text-property left-pos 'crdt-id beg-obj) nil) ;; clear end-of-block flag
    t))

;;; Buffer local variables

(defmacro crdt--defvar-permanent-local (name &optional initial-value docstring)
  "Define a permanent local variable with NAME with INITIAL-VALUE and DOCSTRING."
  (declare (indent 2) (doc-string 3) (debug defvar-local))
  `(progn
     (defvar-local ,name ,initial-value ,docstring)
     (put ',name 'permanent-local t)))

(crdt--defvar-permanent-local crdt--session)

(defsubst crdt--assimilate-session (buffer)
  "Set CRDT--SESSION of BUFFER to be the same as current CRDT--SESSION."
  (let ((session crdt--session))
    (with-current-buffer buffer
      (setq crdt--session session))))

(cl-defstruct (crdt--contact-metadata (:constructor crdt--make-contact-metadata))
  name host service focus)

(cl-defstruct (crdt-remote-fcap
                (:constructor crdt--make-remote-fcap
                              (name nonce in-states out-states interactive-form)))
  name nonce in-states out-states interactive-form)

(cl-defstruct (crdt-local-fcap
                (:constructor crdt--make-local-fcap
                              (name nonce in-states out-states proxy)))
  name nonce in-states out-states proxy)

(cl-defstruct (crdt--session (:constructor crdt--make-session-1))
  local-id                              ; Local user-id
  local-clock                           ; Local logical clock
  (contact-table (make-hash-table))
  ;; A hash table that maps USER-ID to CRDT--CONTACT-METADATAs
  ;; Special case: key nil may be mapped to a metadata for a client
  ;; itself before it gets its user-id. It should be remapped to
  ;; the right key as soon as client knows its user-id
  urlstr
  roger-p ;; set to t when network filter hear any data
  ;; to indicate that TLS handshake (if any) must have completed
  user-menu-buffer
  buffer-menu-buffer
  network-process
  network-clients
  next-user-id
  (buffer-table (make-hash-table :test 'equal)) ; maps buffer network name to buffer
  follow-user-id
  my-location-marker ; used to store my location temporarily when crdt-goto-{next,prev}-user
  permissions
  (local-fcap-table (make-hash-table))
  (remote-fcap-table (make-hash-table)))

(cl-defun crdt--make-session (&rest args &key local-name host service &allow-other-keys)
  (let ((args-1 (cl-copy-list args)))
    (cl-remf args-1 :local-name)
    (cl-remf args-1 :host)
    (cl-remf args-1 :service)
    (let ((session (apply #'crdt--make-session-1 args-1)))
      (puthash (crdt--session-local-id session)
               (crdt--make-contact-metadata :name local-name :host host :service service)
               (crdt--session-contact-table session))
      session)))

(defvar crdt--inhibit-update nil "When set, don't call CRDT--LOCAL-* on change.
This is useful for functions that apply remote change to local buffer,
to avoid recusive calling of CRDT synchronization functions.")

(crdt--defvar-permanent-local crdt--changed-string nil
  "Save changed substring in CRDT--BEFORE-CHANGE.")
(crdt--defvar-permanent-local crdt--changed-start nil
  "Save start character address of changes in CRDT--BEFORE-CHANGE,
to recover the portion being overwritten in CRDT--AFTER-CHANGE.")

(crdt--defvar-permanent-local crdt--last-point nil)
(crdt--defvar-permanent-local crdt--last-mark nil)
(crdt--defvar-permanent-local crdt--last-process-mark-id nil)

(crdt--defvar-permanent-local crdt--pseudo-cursor-table nil
  "A hash table that maps USER-ID to CONSes.
Each element is of the form (CURSOR-OVERLAY . REGION-OVERLAY).")

(crdt--defvar-permanent-local crdt--site-id-table nil
  "A hash table that maps USER-ID to SITE-ID. Only used by the publisher of the buffer.")
(crdt--defvar-permanent-local crdt--site-id-list nil
  "A list of all allocated SITE-ID (except 0 which is reserved for publisher), sorted by value.")
(crdt--defvar-permanent-local crdt--site-id-use-list nil
  "A list of all allocated SITE-ID (except 0 which is reserved for publisher), sorted by recent usage.")
(crdt--defvar-permanent-local crdt--site-id nil "My SITE-ID at this buffer.")

(cl-defstruct (crdt--overlay-metadata
                (:constructor crdt--make-overlay-metadata
                              (lamport-timestamp species front-advance rear-advance plist))
                (:copier crdt--copy-overlay-metadata))
  lamport-timestamp species front-advance rear-advance plist)

(crdt--defvar-permanent-local crdt--overlay-table nil
  "A hash table that maps CONSes of the form (USER-ID . LOGICAL-CLOCK) to overlays.")

(crdt--defvar-permanent-local crdt--buffer-network-name)

(crdt--defvar-permanent-local crdt--buffer-sync-callback)

(crdt--defvar-permanent-local crdt--buffer-pseudo-process)

(defvar crdt--track-overlay-species nil
  "Label any newly created overlay with its value as their ``species''.
You usually want to dynamically bound this variable,
so that overlays created during a dynamic extent
are categorized into the same ``species''.
You can then enable synchronizing those overlays using
function CRDT--ENABLE-OVERLAY-SPECIES.")
(defvar-local crdt--enabled-overlay-species nil
  "A list of ``species'' of overlays that are tracked and synchronized.
See CRDT--TRACK-OVERLAY-SPECIES.
You should always use CRDT--ENABLE-OVERLAY-SPECIES
and CRDT--DISABLE-OVERLAY-SPECIES to modify this variable
as those functions handle bookkeeping of
adding/removing actively tracked overlays.")

(defvar-local crdt--enabled-text-properties '(crdt-author)
  "A list of text properties that are tracked and synchronized.")

;;; Global variables

(defvar crdt--session-list nil)
(defvar crdt--session-menu-buffer nil)

(defvar crdt--process nil
  "Temporarily bound to the current network process when processing messages inside CRDT--NETWORK-FILTER.")

(defvar crdt--remote-call-spawn-user-id nil
  "The User ID where current remote call (if any) is orignally called.")
(defvar crdt--return-message-table (make-hash-table))

(defsubst crdt--client-id ()
  (process-get crdt--process 'client-id))

;;; crdt-mode

(defvar crdt--hooks-alist
  '((after-change-functions . crdt--after-change)
    (before-change-functions . crdt--before-change)
    (post-command-hook . crdt--post-command)
    (deactivate-mark-hook . crdt--post-command)
    (kill-buffer-hook . crdt--kill-buffer-hook)
    (clone-buffer-hook . crdt--clone-buffer-hook)
    (clone-indirect-buffer-hook . crdt--clone-buffer-hook)))

(defun crdt--install-hooks ()
  "Install the hooks used by CRDT-MODE."
  (dolist (pair crdt--hooks-alist)
    (add-hook (car pair) (cdr pair) nil t)))

(defun crdt--uninstall-hooks ()
  "Uninstall the hooks used by CRDT-MODE."
  (dolist (pair crdt--hooks-alist)
    (remove-hook (car pair) (cdr pair) t)))

(defsubst crdt--clear-pseudo-cursor-table ()
  "Remove all overlays in CRDT--PSEUDO-CURSOR-TABLE.
Also set CRDT--PSEUDO-CURSOR-TABLE to NIL."
  (when crdt--pseudo-cursor-table
    (maphash (lambda (_ pair)
               (delete-overlay (car pair))
               (delete-overlay (cdr pair)))
             crdt--pseudo-cursor-table)
    (setq crdt--pseudo-cursor-table nil)))

(defun crdt--after-change-major-mode ()
  "Re-enable CRDT-MODE after major mode change."
  (when (and crdt--session crdt--buffer-network-name
             (eq (current-buffer)
                 (gethash crdt--buffer-network-name
                          (crdt--session-buffer-table crdt--session))))
    (crdt--broadcast-maybe
     (crdt--format-message `(ready ,crdt--buffer-network-name ,major-mode)) nil)
    (crdt-mode)))

(add-hook 'after-change-major-mode-hook #'crdt--after-change-major-mode)

(define-minor-mode crdt-mode
  "Mode for source collaborative buffers."
  :lighter " CRDT"
  (if crdt-mode
      (progn
        (unless crdt--pseudo-cursor-table
          (setq crdt--pseudo-cursor-table (make-hash-table)))
        (unless crdt--overlay-table
          (setq crdt--overlay-table (make-hash-table :test 'equal)))
        (setq crdt--site-id-list (list 0 crdt--max-value))
        (crdt--install-hooks))
    (crdt--uninstall-hooks)
    (crdt--clear-pseudo-cursor-table)
    (setq crdt--overlay-table nil crdt--site-id-list nil
          crdt--buffer-network-name nil)))

(defun crdt--clone-buffer-hook ()
  (crdt-mode -1))

(defvar crdt-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "M-X") #'crdt-M-x)
    map))

(or (assq 'crdt-mode minor-mode-map-alist)
    (nconc minor-mode-map-alist
           (list (cons 'crdt-mode crdt-mode-map))))

;;; Author visualization

(defsubst crdt--visualize-author-1 (beg end user-id)
  (remove-overlays beg end 'category 'crdt-visualize-author)
  (cl-flet ((ov-alike-p (ov)
              (and (eq (overlay-get ov 'category) 'crdt-visualize-author)
                   (eq (overlay-get ov 'crdt-author) user-id))))
    (or
     (let ((ov-front (cl-find-if #'ov-alike-p (overlays-at (1- beg)))))
       (when ov-front (move-overlay ov-front (overlay-start ov-front) end) t))
     (let ((ov-rear (cl-find-if #'ov-alike-p (overlays-at end))))
       (when ov-rear (move-overlay ov-rear beg (overlay-end ov-rear)) t))
     (let ((new-ov (make-overlay beg end nil t nil)))
       (overlay-put new-ov 'category 'crdt-visualize-author)
       (overlay-put new-ov 'crdt-author user-id)
       (overlay-put new-ov 'face `(:background ,(crdt--get-region-color user-id)))))))

(defun crdt--visualize-author ()
  (save-restriction
    (widen)
    (let ((pos (point-max)))
      (while (> pos (point-min))
        (let* ((prev-pos (previous-single-property-change pos 'crdt-author nil (point-min)))
               (user-id (get-text-property prev-pos 'crdt-author)))
          (when user-id (crdt--visualize-author-1 prev-pos pos user-id))
          (setq pos prev-pos))))))

(define-minor-mode crdt-visualize-author-mode
  "Minor mode to visualize who wrote what."
  :lighter " CRDT-VAuthor"
  (if crdt-visualize-author-mode
      (crdt--visualize-author)
    (save-restriction
      (widen)
      (remove-overlays (point-min) (point-max) 'category 'crdt-visualize-author))))

;;; Session state utils

(defsubst crdt--server-p (&optional session)
  "Tell if SESSION is running as a server.
If SESSION is nil, use current CRDT--SESSION."
  (unless session (setq session crdt--session))
  (process-contact (crdt--session-network-process session) :server))

(defsubst crdt--session-local-name (session)
  (crdt--contact-metadata-name
   (gethash (crdt--session-local-id session) (crdt--session-contact-table session))))

(defmacro crdt--session-focused-buffer-name (session)
  `(crdt--contact-metadata-focus
    (gethash (crdt--session-local-id ,session) (crdt--session-contact-table ,session))))

;;; Error recovery

(define-error 'crdt-sync-error "CRDT synchronization error")

(defmacro crdt--with-recover (&rest body)
  "When any error in BODY occur, signal a CRDT-SYNC-ERROR instead.
This will hopefully trigger error recovery mechanism when further unwinding the stack."
  (declare (indent 1) (debug (sexp def-body)))
  `(if crdt--inhibit-recover
       (progn ,@body)
     (condition-case nil
         (progn ,@ body)
       (error (signal 'crdt-sync-error nil)))))

(defmacro crdt--with-should-not-error (name &rest body)
  "When any error in BODY occur, print a report and stop CRDT in this buffer.
NAME is included in the report."
  (declare (indent 1) (debug (sexp def-body)))
  `(if crdt--inhibit-recover
       (progn ,@body)
     (condition-case err
         (progn ,@ body)
       (error
        (warn "CRDT mode exited in buffer %s because of error %s inside %s."
              (current-buffer) err ',name)
        (if (crdt--server-p)
            (crdt-stop-share-buffer)
          (remhash crdt--buffer-network-name (crdt--session-buffer-table crdt--session))
          (crdt--refresh-buffers-maybe)
          (crdt-mode -1))))))

(defun crdt--recover (&optional err)
  "Try to recover from a synchronization failure.
Current buffer is assmuned to be the one with synchronization error.
If we are the server, ERR is the error we shall report to client."
  (if (crdt--server-p)
      (progn
        (let ((message (crdt--format-message `(error ,crdt--buffer-network-name ,(car err) ,(crdt--readable-encode (cdr err))))))
          (process-send-string crdt--process message)))
    (ding)
    (read-only-mode)
    (message "Synchronization error detected, try recovering...")
    (crdt--broadcast-maybe
     (crdt--format-message `(get ,crdt--buffer-network-name)))))

;;; Shared buffer utils

(defun crdt--call-with-buffer-name (name function)
  "Find CRDT shared buffer associated with NAME and call FUNCTION in it.
See `crdt--with-buffer-name'."
  (let (crdt-buffer)
    (setq crdt-buffer (gethash name (crdt--session-buffer-table crdt--session)))
    (when (and crdt-buffer (buffer-live-p crdt-buffer))
      (with-current-buffer crdt-buffer
        (save-restriction
          (widen)
          (condition-case err
              (funcall function)
            (crdt-sync-error (crdt--recover err))))))))

(defmacro crdt--with-buffer-name (name &rest body)
  "Find CRDT shared buffer associated with NAME and evaluate BODY in it.
Any narrowing is temporarily disabled during evaluation of BODY.
Also, try to recover from synchronization error if any error happens in BODY.
Must be called when CURRENT-BUFFER is a CRDT status buffer.
If such buffer doesn't exist yet, do nothing."
  (declare (indent 1) (debug (sexp def-body)))
  `(crdt--call-with-buffer-name ,name (lambda () ,@body)))

(cl-defmacro crdt--with-buffer-name-pull ((name &key sync) &rest body)
  "Find CRDT shared buffer associated with NAME and evaluate BODY in it.
Must be called when CURRENT-BUFFER is a CRDT status buffer.
If such buffer doesn't exist yet, request it from the server,
and store the body in CRDT--BUFFER-SYNC-CALLBACK to evaluate it
after synchronization is completed.
If SYNC is non-nil, block (but allow process filters to run)
until synchronization is completed, otherwise run body asynchronously."
  (declare (indent 1) (debug (sexp def-body)))
  `(let (crdt-buffer)
     (setq crdt-buffer (gethash ,name (crdt--session-buffer-table crdt--session)))
     (if (and crdt-buffer (buffer-live-p crdt-buffer))
         (with-current-buffer crdt-buffer
           ,@body)
       (unless (crdt--server-p)
         (setq crdt-buffer (generate-new-buffer (format "%s<%s>" ,name (crdt--session-urlstr crdt--session))))
         (puthash ,name crdt-buffer (crdt--session-buffer-table crdt--session))
         (let ((session crdt--session))
           (with-current-buffer crdt-buffer
             (setq crdt--buffer-network-name ,name)
             (setq crdt--session session)
             (crdt-mode)
             (crdt--broadcast-maybe (crdt--format-message `(get ,,name)))
             (let ((crdt--inhibit-update t))
               (insert "Synchronizing with server...")
               (read-only-mode))
             ,(if sync
                  `(let (sync-complete)
                     (setq crdt--buffer-sync-callback
                           (lambda () (setq sync-complete t)))
                     (while (not sync-complete)
                       (accept-process-output))
                     ,@body)
                  `(setq crdt--buffer-sync-callback
                         (lambda ()
                           ,@body)))))))))

;;; Session menu

(defsubst crdt--get-session-names (server)
  "Get session names for CRDT sessions (from `crdt--session-list').
If SERVER is non-NIL, return the list of names for server sessions.
Otherwise, return the list of names for client sessions."
  (let (session-names)
    (dolist (session crdt--session-list)
      (when (eq (crdt--server-p session) server)
        (push (crdt--session-urlstr session) session-names)))
    (nreverse session-names)))

(defsubst crdt--get-session (name)
  "Get the CRDT session object with NAME."
  (cl-find name crdt--session-list
           :test 'equal :key #'crdt--session-urlstr))

(defsubst crdt--completing-read (prompt collection &optional initial-input)
  "Like (completing-read PROMPT COLLECTION nil t INITIAL-INPUT).
Do better when there are 0 or 1 candidates."
  (if collection
      (if (cdr collection)
          (completing-read prompt collection nil t initial-input)
        (car collection))
    (signal 'quit "No candidates")))

(defun crdt--read-session (&optional filter)
  "Prompt for a session name and return the corresponding session.
FILTER can be nil, 'server or 'client."
  (crdt--get-session
   (crdt--completing-read
    (format "Choose a%s session: "
            (cl-ecase filter
              ((server) " server")
              ((client) " client")
              ((nil) "")))
    (cl-ecase filter
      ((server) (crdt--get-session-names t))
      ((client) (crdt--get-session-names nil))
      ((nil) (mapcar #'crdt--session-urlstr crdt--session-list)))
    (when (and crdt--session
               (cl-ecase filter
                 ((server) (crdt--server-p))
                 ((client) (not (crdt--server-p)))
                 ((nil) t)))
      (crdt--session-urlstr crdt--session)))))

(defun crdt--read-session-maybe (&optional filter)
  "Prompt for a session name and return the corresponding session.
Directly return the session name under point if in the session menu.
FILTER can be nil, 'server or 'client."
  (if (eq major-mode 'crdt-session-menu-mode)
      (or (tabulated-list-get-id) (signal 'quit nil))
    (if (and crdt--session
             (cl-ecase filter
               ((server) (crdt--server-p))
               ((client) (not (crdt--server-p)))
               ((nil) t)))
        crdt--session
      (or (crdt--read-session filter) (signal 'quit nil)))))

(defvar crdt-session-menu-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'crdt-list-buffers)
    (define-key map [mouse-1] #'crdt-list-buffers)
    (define-key map (kbd "k") #'crdt--stop-session)
    (define-key map (kbd "d") #'crdt--stop-session)
    map))

(define-derived-mode crdt-session-menu-mode tabulated-list-mode
  "CRDT Session List"
  (setq tabulated-list-format [("Session Name" 15 t)
                               ("Role" 7 t)
                               ("My Name" 15 t)
                               ("Buffers" 30 t)
                               ("Users" 15 t)]))

;;;###autoload
(defun crdt-list-sessions (&optional display-buffer)
  "Display a list of active CRDT sessions.
If DISPLAY-BUFFER is provided, display the output there."
  (interactive)
  (unless display-buffer
    (unless (and crdt--session-menu-buffer (buffer-live-p crdt--session-menu-buffer))
      (setf crdt--session-menu-buffer
            (generate-new-buffer "*CRDT Sessions*")))
    (setq display-buffer crdt--session-menu-buffer))
  (crdt-refresh-sessions display-buffer)
  (switch-to-buffer-other-window display-buffer))

(defun crdt-refresh-sessions (display-buffer)
  "Refresh the CRDT session menu in DISPLAY-BUFFER."
  (with-current-buffer display-buffer
    (crdt-session-menu-mode)
    (setq tabulated-list-entries nil)
    (mapc (lambda (session)
            (push
             (list session (vector (crdt--session-urlstr session)
                                   (if (crdt--server-p session) "Server" "Client")
                                   (crdt--session-local-name session)
                                   (mapconcat (lambda (v) (format "%s" v))
                                              (hash-table-keys (crdt--session-buffer-table session))
                                              ", ")
                                   (mapconcat (lambda (v) (format "%s" v))
                                              (mapcar #'crdt--contact-metadata-name
                                                      (hash-table-values (crdt--session-contact-table session)))
                                              ", ")))
             tabulated-list-entries))
          crdt--session-list)
    (tabulated-list-init-header)
    (tabulated-list-print)))

(defsubst crdt--refresh-sessions-maybe ()
  "Refresh the session menu buffer, if there's any."
  (when (and crdt--session-menu-buffer (buffer-live-p crdt--session-menu-buffer))
    (crdt-refresh-sessions crdt--session-menu-buffer)))

;;; Buffer menu

(defun crdt--read-buffer (session)
  "Prompt for a buffer network name in SESSION."
  (crdt--completing-read
   "Choose a buffer: "
   (hash-table-keys (crdt--session-buffer-table session))
   (when (and (eq crdt--session session)
              crdt--buffer-network-name)
     crdt--buffer-network-name)))

(defun crdt--read-buffer-maybe (session)
  "Prompt for a buffer network name in SESSION.
Directly return the buffer network name under point if in the buffer menu."
  (or (and (eq crdt--session session)
           (if (eq major-mode 'crdt-buffer-menu-mode)
               (or (tabulated-list-get-id) (signal 'quit nil))
             crdt--buffer-network-name))
      (crdt--read-buffer session)
      (signal 'quit nil)))

(defun crdt-switch-to-buffer-other-window (session network-name)
  "Open buffer with NETWORK-NAME in SESSION."
  (interactive
   (let ((session (crdt--read-session-maybe)))
     (list session (crdt--read-buffer-maybe session))))
  (let ((crdt--session session))
    (crdt--with-buffer-name-pull (network-name)
      (switch-to-buffer-other-window (current-buffer)))))

(defvar crdt-buffer-menu-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'crdt-switch-to-buffer-other-window)
    (define-key map [mouse-1] #'crdt-switch-to-buffer-other-window)
    (define-key map (kbd "k") #'crdt-stop-share-buffer)
    (define-key map (kbd "d") #'crdt-stop-share-buffer)
    map))

(define-derived-mode crdt-buffer-menu-mode tabulated-list-mode
  "CRDT Buffer List"
  (setq tabulated-list-format [("Local Buffer" 15 t)
                               ("Network Name" 30 t)
                               ("Users" 15 t)]))

;;;###autoload
(defun crdt-list-buffers (&optional session)
  "Display a list of buffers shared in SESSION."
  (interactive (list (crdt--read-session-maybe)))
  (let ((crdt--session (or session crdt--session)))
    (with-current-buffer (current-buffer)
      (unless crdt--session
        (error "Not a CRDT shared buffer"))
      (unless (and (crdt--session-buffer-menu-buffer crdt--session) (buffer-live-p (crdt--session-buffer-menu-buffer crdt--session)))
        (setf (crdt--session-buffer-menu-buffer crdt--session)
              (generate-new-buffer (format "*CRDT Buffers %s*" (crdt--session-urlstr crdt--session))))
        (crdt--assimilate-session (crdt--session-buffer-menu-buffer crdt--session)))
      (let ((display-buffer (crdt--session-buffer-menu-buffer crdt--session)))
        (crdt-refresh-buffers display-buffer)
        (if (crdt--session-network-process crdt--session)
            (switch-to-buffer display-buffer)
          (switch-to-buffer-other-window display-buffer))))))

(defun crdt-refresh-buffers (display-buffer)
  "Refresh the CRDT buffer menu in DISPLAY-BUFFER."
  (with-current-buffer display-buffer
    (crdt-buffer-menu-mode)
    (setq tabulated-list-entries nil)
    (let ((tmp-hashtable (make-hash-table :test 'equal)))
      (maphash (lambda (_ v)
                 (push (crdt--contact-metadata-name v)
                       (gethash (crdt--contact-metadata-focus v)
                                tmp-hashtable)))
               (crdt--session-contact-table crdt--session))
      (maphash (lambda (k v)
                 (push (list k (vector (if (and v (buffer-live-p v))
                                           (buffer-name v)
                                         "--")
                                       k (mapconcat #'identity (gethash k tmp-hashtable) ", ")))
                       tabulated-list-entries))
               (crdt--session-buffer-table crdt--session)))
    (tabulated-list-init-header)
    (tabulated-list-print)))

(defsubst crdt--refresh-buffers-maybe ()
  "Refresh the buffer menu buffer for current session, if there's any."
  (when (and (crdt--session-buffer-menu-buffer crdt--session) (buffer-live-p (crdt--session-buffer-menu-buffer crdt--session)))
    (crdt-refresh-buffers (crdt--session-buffer-menu-buffer crdt--session)))
  (crdt--refresh-sessions-maybe))

;;; User menu

(defun crdt--read-user (session)
  "Prompt for a user name in SESSION."
  (let (candidates)
    (maphash
     (lambda (k v)
       (push (format "%s %s" k (crdt--contact-metadata-name v)) candidates))
     (crdt--session-contact-table session))
    (let ((name
           (crdt--completing-read "Choose a user: " candidates)))
      (string-to-number (car (split-string name))))))

(defun crdt--read-user-maybe (session)
  "Prompt for a user name in SESSION.
Directly return the user name under point if in the user menu."
  (or (and (eq crdt--session session)
           (eq major-mode 'crdt-user-menu-mode)
           (or (tabulated-list-get-id) (signal 'quit nil)))
      (crdt--read-user session)
      (signal 'quit nil)))

(defun crdt-goto-user (session user-id)
  "Goto the cursor location of user with USER-ID in SESSION."
  (interactive (let ((session (crdt--read-session-maybe)))
                 (list session (crdt--read-user-maybe session))))
  (let ((crdt--session session)
        (switch-window-function
         (if (eq major-mode 'crdt-user-menu-mode) #'switch-to-buffer-other-window #'switch-to-buffer)))
    (if (eq user-id (crdt--session-local-id crdt--session))
        (funcall switch-window-function
                 (gethash (crdt--session-focused-buffer-name crdt--session) (crdt--session-buffer-table crdt--session)))
      (unless
          (cl-block nil
            (let* ((metadata (or (gethash user-id (crdt--session-contact-table crdt--session)) (cl-return)))
                   (buffer-name (or (crdt--contact-metadata-focus metadata) (cl-return))))
              (crdt--with-buffer-name-pull (buffer-name)
                (funcall switch-window-function (current-buffer))
	        (ignore-errors (goto-char (overlay-start (car (gethash user-id crdt--pseudo-cursor-table)))))
	        t)))
        (message "Doesn't have position information for this user yet.")))))

(defun crdt--session-ensure-user-menu-buffer (session)
  (unless (and (crdt--session-user-menu-buffer session)
               (buffer-live-p (crdt--session-user-menu-buffer session)))
    (setf (crdt--session-user-menu-buffer session)
          (generate-new-buffer (format "*CRDT Users %s*" (crdt--session-urlstr session))))
    (crdt--assimilate-session (crdt--session-user-menu-buffer session))))

(defun crdt--cycle-user (&optional prev)
  "Move point in user menu buffer and goto its cursor position.
If user menu buffer does not exist yet, create it.
If PREV is non-nil, move backward, otherwise move forward.
When moving into/out of ourselves, push/pop a global marker instead."
  (unless crdt--session
    (error "Not a CRDT shared buffer"))
  (crdt--session-ensure-user-menu-buffer crdt--session)
  (let* ((mark (point-marker))
         (user-id
          (with-current-buffer (crdt--session-user-menu-buffer crdt--session)
            (when (= (point) (point-max))
              (forward-line -1))
            (when (eq (tabulated-list-get-id) (crdt--session-local-id crdt--session))
              (setf (crdt--session-my-location-marker crdt--session) mark)
              (add-to-history 'global-mark-ring mark global-mark-ring-max t))
            (if prev
                (unless (= (forward-line -1) 0)
                  (goto-char (point-max))
                  (forward-line -1))
              (forward-line)
              (when (= (point) (point-max))
                (goto-char (point-min))))
            (let ((window (get-buffer-window (current-buffer) t)))
              (when window (set-window-point window (point))))
            (if (eq (tabulated-list-get-id) (crdt--session-local-id crdt--session))
                (when (crdt--session-my-location-marker crdt--session)
                  (if (eq (car global-mark-ring) (crdt--session-my-location-marker crdt--session))
                      (pop-global-mark)
                    (goto-char (crdt--session-my-location-marker crdt--session)))
                  nil)
              (tabulated-list-get-id)))))
    (when user-id (crdt-goto-user crdt--session user-id))))

(defun crdt-goto-next-user ()
  "Move point in user menu buffer to next user and goto its cursor position.
If user menu buffer does not exist yet, create it."
  (interactive)
  (crdt--cycle-user))

(defun crdt-goto-prev-user ()
  "Move point in user menu buffer to previous user and goto its cursor position.
If user menu buffer does not exist yet, create it."
  (interactive)
  (crdt--cycle-user t))

(defun crdt-kill-user (session user-id)
  "Disconnect the user with USER-ID in SESSION.
Only server can perform this action."
  (interactive (let ((session (crdt--read-session-maybe 'server)))
                 (list session (crdt--read-user-maybe session))))
  (let ((crdt--session session))
    (if (crdt--server-p)
        (if (eq user-id (crdt--session-local-id crdt--session))
            (error "Suicide is not allowed")
          (dolist (p (process-list))
            (when (eq (process-get p 'client-id) user-id)
              (delete-process p))))
      (message "Only server can disconnect a user."))))

(defvar crdt-user-menu-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "RET") #'crdt-goto-user)
    (define-key map [mouse-1] #'crdt-goto-user)
    (define-key map (kbd "k") #'crdt-kill-user)
    (define-key map (kbd "d") #'crdt-kill-user)
    (define-key map (kbd "f") #'crdt-follow-user)
    map))

(define-derived-mode crdt-user-menu-mode tabulated-list-mode
  "CRDT User List"
  (setq tabulated-list-format [("ID" 7 t)
                               ("Display Name" 15 t)
                               ("Follow" 7 t)
                               ("Focused Buffer" 30 t)]))

;;;###autoload
(defun crdt-list-users (&optional session)
  "Display a list of active users working on a SESSION."
  (interactive (list (crdt--read-session-maybe)))
  (let ((crdt--session session))
    (with-current-buffer (current-buffer)
      (unless crdt--session
        (error "Not a CRDT shared buffer"))
      (crdt--session-ensure-user-menu-buffer crdt--session)
      (let ((display-buffer (crdt--session-user-menu-buffer crdt--session)))
        (crdt-refresh-users display-buffer)
        (switch-to-buffer-other-window display-buffer)))))

(defun crdt-refresh-users (display-buffer)
  "Refresh the CRDT user menu in DISPLAY-BUFFER."
  (with-current-buffer display-buffer
    (crdt-user-menu-mode)
    (setq tabulated-list-entries nil)
    (maphash (lambda (k v)
               (push (list k (let ((name (crdt--contact-metadata-name v))
                                   (focused-buffer-name (or (crdt--contact-metadata-focus v) "--")))
                               (let ((colored-name (concat name " ")))
                                 (put-text-property 0 (1- (length colored-name))
                                                    'face `(:background ,(crdt--get-region-color k))
                                                    colored-name)
                                 (put-text-property (1- (length colored-name)) (length colored-name)
                                                    'face `(:background ,(crdt--get-cursor-color k))
                                                    colored-name)
                                 (vector (prin1-to-string k) colored-name
                                         (if (eq k (crdt--session-follow-user-id crdt--session))
                                             "yes" "")
                                         focused-buffer-name))))
                     tabulated-list-entries))
             (crdt--session-contact-table crdt--session))
    (tabulated-list-init-header)
    (tabulated-list-print)))

(defsubst crdt--refresh-users-maybe ()
  "Refresh the user menu buffer for current session, if there's any.
This function also calls `crdt--refresh-buffers-maybe', as changes in
user menu almost always indicate supposed changes in buffer menu."
  (when (and (crdt--session-user-menu-buffer crdt--session) (buffer-live-p (crdt--session-user-menu-buffer crdt--session)))
    (crdt-refresh-users (crdt--session-user-menu-buffer crdt--session)))
  (crdt--refresh-buffers-maybe))

(defun crdt-follow-user (session user-id)
  "Toggle following user with USER-ID in SESSION."
  (interactive (let ((session (crdt--read-session-maybe)))
                 (list session (crdt--read-user-maybe session))))
  (let ((crdt--session session))
    (if (eq user-id (crdt--session-local-id crdt--session))
        (error "Narcissism is not allowed")
      (if (eq user-id (crdt--session-follow-user-id crdt--session))
          (crdt-stop-follow)
        (setf (crdt--session-follow-user-id crdt--session) user-id))
      (crdt--refresh-users-maybe))))

(defun crdt-stop-follow ()
  "Stop following user if any."
  (interactive)
  (message "Stop following %s."
           (crdt--contact-metadata-name
            (gethash (crdt--session-follow-user-id crdt--session)
                     (crdt--session-contact-table crdt--session))))
  (setf (crdt--session-follow-user-id crdt--session) nil)
  (crdt--refresh-users-maybe))

(defun crdt--kill-buffer-hook ()
  "Kill buffer hook for CRDT shared buffers.
It informs other peers that the buffer is killed."
  (when crdt--buffer-network-name
    (puthash crdt--buffer-network-name nil (crdt--session-buffer-table crdt--session))
    (crdt--broadcast-maybe (crdt--format-message
                            `(cursor ,crdt--buffer-network-name
                                     ,(crdt--session-local-id crdt--session) nil nil nil nil)))
    (when (eq (crdt--session-focused-buffer-name crdt--session) crdt--buffer-network-name)
      (crdt--broadcast-maybe (crdt--format-message
                              `(contact ,(crdt--session-local-id crdt--session) focus nil)))
      (setf (crdt--session-focused-buffer-name crdt--session) nil))
    (when (crdt--server-p)
      (crdt-stop-share-buffer))
    (crdt--refresh-users-maybe)))

;;; Capabilities

(define-error 'crdt-invalid-fcap "Invalid CRDT fcap")
(define-error 'crdt-no-permission "No CRDT permission")

(defsubst crdt-get-fcap (fcap-symbol)
  "Find the active `crdt-remote-fcap' with name FCAP-SYMBOL.
Signal a `crdt-no-permission' error if no such fcap exists."
  (or (and crdt--session (gethash fcap-symbol (crdt--session-remote-fcap-table crdt--session)))
      (signal 'crdt-no-permission (list fcap-symbol))))

(cl-defun crdt-make-local-fcap
    (name &optional in-states out-states (proxy name))
  "Return a new `crdt-local-fcap'.
The fcap is initialized with NAME, IN-STATES, OUT-STATES and PROXY.
When PROXY is nil, use NAME by default."
  (crdt--make-local-fcap name nil in-states out-states proxy))

(defun crdt-make-local-fcaps (fcap-entries)
  "Return a list of new `crdt-local-fcap'.
FCAP-ENTRIES should be a list with each element a valid lists
of arguments to `crdt-make-local-fcap'.
See `crdt-xscheme-fcaps' for an example of usage."
  (mapcar (lambda (entry) (apply #'crdt-make-local-fcap entry))
          fcap-entries))

(defun crdt--generate-nonce ()
  (with-temp-buffer
    (toggle-enable-multibyte-characters 0)
    (let ((err (call-process-shell-command "head -c 16 /dev/urandom" nil t)))
      (unless (= err 0)
        (error "Failed to read /dev/urandom (code %s)" err)))
    (buffer-string)))

(defun crdt--compute-user-fcaps (permission user-id)
  (cl-loop for f in permission
        if (functionp f)
        append (funcall f user-id)
        else if (symbolp f)
        append (symbol-value f)
        else
        append f))

(defun crdt--intern-fcap (fcap)
  "Copy FCAP to current session's local fcap table.
Generate a nonce if none has been generated before."
  (let ((memo (gethash (crdt-local-fcap-name fcap)
                       (crdt--session-local-fcap-table crdt--session)))
        (fcap (cl-copy-seq fcap)))
    (setf (crdt-local-fcap-nonce fcap)
          (if memo (crdt-local-fcap-nonce memo) (crdt--generate-nonce)))
    (puthash (crdt-local-fcap-name fcap) fcap
             (crdt--session-local-fcap-table crdt--session))
    fcap))

(defun crdt-make-interactive-proxy (command-symbol)
  "Return a function that calls COMMAND-SYMBOL interactively on remote machine."
  (lambda () (interactive)
    (let ((this-command command-symbol))
      (call-interactively command-symbol))))

(defun crdt-get-write-access ()
  "Allocate a Site ID for current user to access current buffer.
Current user means the user corresponding to CRDT--PROCESS."
  (let (new-site-id)
    (cl-loop
          for i in crdt--site-id-list
          for c on crdt--site-id-list
          for j in (cdr crdt--site-id-list)
          if (> j (1+ i))
          do (progn
               (setq new-site-id (1+ i))
               (push (1+ i) (cdr c))
               (cl-return)))
    (unless new-site-id
      (let* ((cons (last crdt--site-id-use-list 2))
             (victim-id (cadr cons)))
        ;; todo: notify the victim
        (rplacd cons nil)
        (setq new-site-id victim-id)))
    (push new-site-id crdt--site-id-use-list)
    (puthash (crdt--client-id) new-site-id crdt--site-id-table)
    new-site-id))

(defvar crdt-write-access-fcaps
  (crdt-make-local-fcaps '((crdt-get-write-access (buffer)))))

(defun crdt-get-buffer-create (network-name)
  "Return the buffer with NETWORK-NAME, creating a new one if needed."
  (or (gethash network-name (crdt--session-buffer-table crdt--session))
      (crdt--share-buffer (generate-new-buffer network-name)
                          crdt--session network-name)))

(defvar crdt-create-buffer-fcaps
  (crdt-make-local-fcaps '((crdt-get-buffer-create))))

;;; CRDT insert/delete

(defsubst crdt--text-property-assimilate
    (template template-beg template-end beg prop &optional object)
  "Make PROP after BEG in OBJECT the same as part of TEMPLATE.
The part between TEMPLATE-BEG and TEMPLATE-END is used.
If OBJECT is NIL, use current buffer."
  (let (next-pos
        (pos template-beg)
        (limit template-end)
        (offset (- beg template-beg)))
    (while (< pos limit)
      (setq next-pos (next-single-property-change pos prop template limit))
      (put-text-property (+ offset pos) (+ offset next-pos) prop
                         (get-text-property pos prop template)
                         object)
      (setq pos next-pos))))

(defsubst crdt--buffer-substring (beg end)
  "Return the contents between BEG and END of the current buffer as a string.
Copies text properties in CRDT--ENABLED-TEXT-PROPERTIES."
  (let ((string (buffer-substring-no-properties beg end)))
    (dolist (prop crdt--enabled-text-properties)
      (crdt--text-property-assimilate nil beg end 0 prop string))
    string))

(defun crdt--local-insert (beg end)
  "To be called after a local insert happened in current buffer from BEG to END.
Returns a list of (insert type) messages to be sent."
  (let* ((user-id (crdt--session-local-id crdt--session)))
    (unless crdt--site-id
      (error "No write permission"))
    (put-text-property beg end 'crdt-author user-id)
    (when crdt-visualize-author-mode
      (crdt--visualize-author-1 beg end user-id))
    (let (resulting-fcaps)
      (crdt--with-insertion-information (beg end)
        (unless (crdt--split-maybe)
	  (when (and not-begin
                     (eq (crdt--id-site starting-id) (crdt--session-local-id crdt--session))
                     (crdt--end-of-block-p left-pos))
            ;; merge crdt id block
            (let* ((max-offset crdt--max-value)
                   (merge-end (min end (+ (- max-offset left-offset 1) beg))))
              (unless (= merge-end beg)
                (put-text-property beg merge-end 'crdt-id starting-id-pair)
                (let ((virtual-id (substring starting-id)))
		  (crdt--set-id-offset virtual-id (1+ left-offset))
		  (push `(insert ,crdt--buffer-network-name ,user-id
                                 ,virtual-id ,beg
                                 ,(crdt--buffer-substring beg merge-end))
                        resulting-fcaps))
                (cl-incf left-offset (- merge-end beg))
                (setq beg merge-end)))))
        (while (< beg end)
	  (let ((block-end (min end (+ crdt--max-value beg))))
            (let* ((ending-id (if not-end (crdt--get-starting-id end) ""))
                   (new-id (crdt--generate-id starting-id left-offset
                                              ending-id (if not-end (crdt--id-offset ending-id) 0)
                                              crdt--site-id)))
              (put-text-property beg block-end 'crdt-id (cons new-id t))
              (push `(insert ,crdt--buffer-network-name ,user-id
                             ,new-id ,beg
                             ,(crdt--buffer-substring beg block-end))
                    resulting-fcaps)
              (setq beg block-end)
              (setq left-offset (1- crdt--max-value)) ; this is always true when we need to continue
              (setq starting-id new-id)))))
      ;; (crdt--verify-buffer)
      (nreverse resulting-fcaps))))

(defun crdt--find-id (id pos &optional before)
  "Find the first position *after* ID if BEFORE is NIL or *before* ID otherwise.
Start the search from POS.
This function doesn't handle empty string convention in the crdt.el protocol.
To convert an ID in protocol message to a position in the buffer,
CRDT--ID-TO-POS is usually more appropriate."
  (let* ((left-pos (previous-single-property-change (min (1+ pos) (point-max))
                                                    'crdt-id nil (point-min)))
         (left-id (crdt--get-starting-id left-pos))
         (right-pos (next-single-property-change (min pos (point-max)) 'crdt-id nil (point-max)))
         (right-id (crdt--get-starting-id right-pos))
         (moving-forward nil))
    (cl-macrolet ((move-forward ()
                    '(progn
                      (setq moving-forward t)
                      (setq left-pos right-pos)
                      (setq left-id right-id)
                      (setq right-pos (next-single-property-change right-pos 'crdt-id nil (point-max)))
                      (setq right-id (crdt--get-starting-id right-pos))))
                  (move-backward ()
                    '(progn
                      (setq moving-forward nil)
                      (setq right-pos left-pos)
                      (setq right-id left-id)
                      (setq left-pos (previous-single-property-change left-pos 'crdt-id nil (point-min)))
                      (setq left-id (crdt--get-starting-id left-pos)))))
      (cl-block nil
        (while t
          (cond ((<= right-pos (point-min))
                 (cl-return (point-min)))
                ((>= left-pos (point-max))
                 (cl-return (point-max)))
                ((and right-id (not (string< id right-id)))
                 (move-forward))
                ((not left-id)
                 (if moving-forward
                     (move-forward)
                   (move-backward)))
                ((string< id left-id)
                 (move-backward))
                (t
                 ;; will unibyte to multibyte conversion cause any problem?
                 (cl-return
                   (if (eq t (compare-strings left-id 0 (- (string-bytes left-id) 2)
                                              id 0 (- (string-bytes left-id) 2)))
                       (min right-pos (+ left-pos (if before 0 1)
                                         (- (crdt--get-two-bytes id (- (string-bytes left-id) 2))
                                            (crdt--id-offset left-id))))
                     right-pos)))))))))

(defun crdt--remote-insert (id user-id position-hint content)
  "Handle remote insert message that CONTENT should be insert.
The first character of CONTENT has CRDT ID.
Start the search around POSITION-HINT.
Mark the insertion as authored by USER-ID."
  (let* ((beg (crdt--find-id id position-hint)) end)
    (save-excursion
      (goto-char beg)
      (insert (propertize content 'crdt-author user-id))
      (setq end (point))
      (when crdt-visualize-author-mode
        (crdt--visualize-author-1 beg end (crdt--id-site id)))
      ;; work around for input method overlays
      (cl-loop for ov in (overlays-at beg)
            do (unless (or (overlay-get ov 'crdt-meta)
                           (memq (overlay-get ov 'category)
                                 '(crdt-visualize-author crdt-pseudo-cursor)))
                 (when (eq (overlay-start ov) beg)
                   (move-overlay ov end (overlay-end ov)))))
      (with-silent-modifications
        (let ((real-end end))
          (unless (get-text-property end 'crdt-id)
            (setq end (next-single-property-change end 'crdt-id nil (point-max))))
          (crdt--with-insertion-information (beg end)
           (let ((base-length (- (string-bytes starting-id) 2)))
             (if (and (eq (string-bytes id) (string-bytes starting-id))
                      (eq t (compare-strings starting-id 0 base-length
                                             id 0 base-length))
                      (eq (1+ left-offset) (crdt--id-offset id)))
                 (put-text-property beg real-end 'crdt-id starting-id-pair)
               (put-text-property beg real-end 'crdt-id (cons id t))))
           (crdt--split-maybe))))))
  ;; (crdt--verify-buffer)
  )

(defsubst crdt--changed-string (beg length)
  "Retrieve part of CRDT--CHANGED-STRING starting at BEG with LENGTH before change."
  (let ((from (- beg crdt--changed-start)))
    (substring crdt--changed-string from (+ from length))))

(defun crdt--local-delete (beg end length)
  "Handle local deletion event and return a message to be sent to other peers.
The deletion happens between BEG and END, and have LENGTH."
  (let ((outer-end end)
        (crdt--changed-string (crdt--changed-string beg length)))
    (crdt--with-insertion-information (beg 0 nil crdt--changed-string nil (length crdt--changed-string))
      (when (crdt--split-maybe)
	(let* ((not-end (< outer-end (point-max)))
               (ending-id (when not-end (crdt--get-starting-id outer-end))))
          (when (and not-end (eq starting-id (crdt--get-starting-id outer-end)))
            (crdt--set-id outer-end
                          (crdt--id-replace-offset ending-id (+ 1 left-offset (length crdt--changed-string))))))))
    (crdt--with-insertion-information ((length crdt--changed-string) outer-end crdt--changed-string nil 0 nil)
      (crdt--split-maybe))
    ;; (crdt--verify-buffer)
    `(delete ,crdt--buffer-network-name ,(crdt--session-local-id crdt--session)
             ,beg ,@ (crdt--dump-ids 0 (length crdt--changed-string) crdt--changed-string t))))

(defun crdt--remote-delete (position-hint id-items)
  "Handle remote deletion message of ID-ITEMS.
ID-ITEMS should be a list of CONSes of the form (LENGTH . STARTING-ID).
Start the search for those ID-ITEMs around POSITION-HINT."
  (save-excursion
    (dolist (id-item id-items)
      (cl-destructuring-bind (length id) id-item
        (while (> length 0)
          (goto-char (crdt--find-id id position-hint t))
          (let* ((end-of-block (next-single-property-change (point) 'crdt-id nil (point-max)))
                 (block-length (- end-of-block (point))))
            (cl-case (cl-signum (- length block-length))
              ((1) (delete-char block-length)
               (cl-decf length block-length)
               (crdt--set-id-offset id (+ (crdt--id-offset id) block-length)))
              ((0) (delete-char length)
               (setq length 0))
              ((-1)
               (let* ((starting-id (crdt--get-starting-id (point)))
                      (eob (crdt--end-of-block-p (point)))
                      (left-offset (crdt--get-id-offset starting-id (point))))
                 (delete-char length)
                 (crdt--set-id (point) (crdt--id-replace-offset starting-id (+ left-offset length)) eob))
               (setq length 0)))))
        ;; (crdt--verify-buffer)
        ))))

(defun crdt--before-change (beg end)
  "Before change hook used by CRDT-MODE.
Save the content to be changed (between BEG and END) into CRDT--CHANGED-STRING.
Request a Site ID if we don't have it yet."
  (unless crdt--inhibit-update
    (setq crdt--changed-string (crdt--buffer-substring beg end))
    (crdt--text-property-assimilate nil beg end 0
                                    'crdt-id crdt--changed-string)
    (setq crdt--changed-start beg)
    (unless crdt--site-id
      (condition-case nil
          (setq crdt--site-id
                (crdt-remote-apply (crdt-get-fcap 'crdt-get-write-access) nil))
        (crdt-invalid-fcap
         (read-only-mode)
         (warn "Write access revoked in %s" crdt--buffer-network-name)
         (signal 'quit nil))))))

(defsubst crdt--crdt-id-assimilate (template beg &optional object)
  "Make the CRDT-ID property after BEG in OBJECT the same as TEMPLATE.
TEMPLATE should be a string.  If OBJECT is NIL, use current buffer."
  (crdt--text-property-assimilate template 0 (length template) beg 'crdt-id object))

(defun crdt--after-change (beg end length)
  "After change hook used by CRDT-MODE.
It examine (CRDT--CHANGED-STRING) (should be saved by CRDT--BEFORE-STRING)
and current content between BEG and END with LENGTH,
update the CRDT-ID for any newly inserted text, and send message to other peers if needed."
  (crdt--with-should-not-error 'crdt--after-change
    (when (markerp beg)
      (setq beg (marker-position beg)))
    (when (markerp end)
      (setq end (marker-position end)))
    (mapc (lambda (ov)
            (when (eq (overlay-get ov 'category) 'crdt-pseudo-cursor)
              (crdt--move-cursor ov beg)))
          (overlays-in beg (min (point-max) (1+ beg))))
    (when (crdt--session-local-id crdt--session)
      (unless crdt--inhibit-update
        (let ((crdt--inhibit-update t))
          ;; we're only interested in text change
          ;; ignore property only changes
          ;; todo: track properties in crdt--enabled-text-properties
          (save-excursion
            (save-restriction
              (goto-char beg)
              (if (and (= length (- end beg))
                       (equal-including-properties (crdt--changed-string beg length)
                                                   (crdt--buffer-substring beg end)))
                  (crdt--crdt-id-assimilate (crdt--changed-string beg length) beg)
                (widen)
                (with-silent-modifications
                  (unless (= length 0)
                    (crdt--broadcast-maybe
                     (crdt--format-message (crdt--local-delete beg end length))))
                  (unless (= beg end)
                    (dolist (message (crdt--local-insert beg end))
                      (crdt--broadcast-maybe
                       (crdt--format-message message))))))))
          ;; see if region stuff changed
          (let ((cursor-message (crdt--local-cursor)))
            (when cursor-message
              (crdt--broadcast-maybe (crdt--format-message cursor-message))))
          ;; process-mark synchronization is dependent on correct CRDT-ID
          ;; therefore we must do it after the insert/change stuff is done
          (crdt--send-process-mark-maybe)
          (crdt--send-variables-maybe))))))

;;; CRDT point/mark synchronization

(defsubst crdt--id-to-pos (id hint)
  "Convert CRDT-ID ID to a position in current buffer with best effort.
Start the search around HINT."
  (if (> (string-bytes id) 0)
      (crdt--find-id id hint t)
    (point-max)))

(defun crdt--remote-cursor (user-id point-position-hint point-crdt-id mark-position-hint mark-crdt-id)
  "Handle remote cursor/mark movement message at USER-ID.
The cursor for that site is at POINT-CRDT-ID,
whose search starts around POINT-POSITION-HINT.
If POINT-CRDT-ID is NIL, remove the pseudo cursor and region
overlays for this site.
The mark for that site is at MARK-CRDT-ID,
whose search starts around MARK-POSITION-HINT.
If MARK-CRDT-ID is NIL, deactivate the pseudo region overlay."
  (when (and user-id (not (eq user-id (crdt--session-local-id crdt--session))))
    (let ((ov-pair (gethash user-id crdt--pseudo-cursor-table)))
      (if point-crdt-id
          (let* ((point (crdt--id-to-pos point-crdt-id point-position-hint))
                 (mark (if mark-crdt-id
                           (crdt--id-to-pos mark-crdt-id mark-position-hint)
                         point)))
            (unless ov-pair
              (let ((new-cursor (make-overlay 1 1))
                    (new-region (make-overlay 1 1)))
                (overlay-put new-cursor 'face `(:background ,(crdt--get-cursor-color user-id)))
                (overlay-put new-cursor 'category 'crdt-pseudo-cursor)
                (overlay-put new-region 'face `(:background ,(crdt--get-region-color user-id) :extend t))
                (setq ov-pair (puthash user-id (cons new-cursor new-region)
                                       crdt--pseudo-cursor-table))))
            (crdt--move-cursor (car ov-pair) point)
            (crdt--move-region (cdr ov-pair) point mark)
            (when (eq user-id (crdt--session-follow-user-id crdt--session))
              (goto-char point)
              (let ((cursor-message (crdt--local-cursor)))
                (when cursor-message
                  (crdt--broadcast-maybe (crdt--format-message cursor-message))))))
        (when ov-pair
          (remhash user-id crdt--pseudo-cursor-table)
          (delete-overlay (car ov-pair))
          (delete-overlay (cdr ov-pair)))))))

(cl-defun crdt--local-cursor (&optional (lazy t))
  "Handle local cursor/mark movement event.
If LAZY if T, return NIL if cursor/mark doesn't move
since last call of this function.
Always return a message otherwise."
  (let ((point (point))
        (mark (when (use-region-p) (mark))))
    (unless (and lazy
                 (eq point crdt--last-point)
                 (eq mark crdt--last-mark))
      (when (or (eq point (point-max)) (eq crdt--last-point (point-max)))
        (mapc (lambda (ov)
                (when (eq (overlay-get ov 'category) 'crdt-pseudo-cursor)
                  (crdt--move-cursor ov (point-max))))
              (overlays-in (point-max) (point-max))))
      (setq crdt--last-point point)
      (setq crdt--last-mark mark)
      (save-restriction
        (widen)
        `(cursor ,crdt--buffer-network-name ,(crdt--session-local-id crdt--session)
                 ,point ,(crdt--get-id point) ,mark ,(when mark (crdt--get-id mark)))))))

(defun crdt--post-command ()
  "Post command hook used by CRDT-MODE.
Check if focused buffer and cursor/mark position are changed.
Send message to other peers about any changes."
  (crdt--with-should-not-error crdt--post-command
    ;; CRDT--BEFORE-CHANGE may have sacrificed itself to interrupt a write attempt
    ;; add it back to BEFORE-CHANGE-FUNCTIONS
    (add-to-list 'before-change-functions 'crdt--before-change)
    (unless (eq crdt--buffer-network-name (crdt--session-focused-buffer-name crdt--session))
      (crdt--broadcast-maybe
       (crdt--format-message `(contact ,(crdt--session-local-id crdt--session) focus ,crdt--buffer-network-name)))
      (setf (crdt--session-focused-buffer-name crdt--session) crdt--buffer-network-name)
      (crdt--refresh-users-maybe))
    (let ((cursor-message (crdt--local-cursor)))
      (when cursor-message
        (crdt--broadcast-maybe (crdt--format-message cursor-message))))
    ;; process-mark synchronization is dependent on correct CRDT-ID
    ;; therefore we must do it after the insert/change stuff is done
    (crdt--send-process-mark-maybe)
    (crdt--send-variables-maybe)))

;;; CRDT ID (de)serialization

(defun crdt--dump-ids (beg end object &optional omit-end-of-block-p include-content)
  "Serialize all CRDT IDs in OBJECT from BEG to END into a list.
The list contains CONSes of the form (LENGTH CRDT-ID END-OF-BLOCK-P),
or (LENGTH CRDT-ID) if OMIT-END-OF-BLOCK-P is non-NIL,
in the order that they appears in the document.
If INCLUDE-CONTENT is non-NIL, the list contains STRING instead of LENGTH."
  (let (ids (pos end))
    (while (> pos beg)
      (let ((prev-pos (previous-single-property-change pos 'crdt-id object beg)))
        (when (crdt--get-crdt-id-pair prev-pos object)
          (push (cons (if include-content
                          (cond ((not object) (crdt--buffer-substring prev-pos pos))
                                ((bufferp object)
                                 (with-current-buffer object
                                   (crdt--buffer-substring prev-pos pos)))
                                (t (substring object prev-pos pos)))
                        (- pos prev-pos))
                      (cl-destructuring-bind (id . eob) (crdt--get-crdt-id-pair prev-pos object)
                        (if omit-end-of-block-p (list id) (list id eob))))
                ids))
        (setq pos prev-pos)))
    ids))

(defun crdt--load-ids (ids)
  "Load the CRDT ids in IDS (generated by CRDT--DUMP-IDS)
into current buffer."
  (goto-char (point-min))
  (dolist (id-item ids)
    (cl-destructuring-bind (content id eob) id-item
      (insert (propertize content 'crdt-id (cons id eob))))))

(defun crdt--verify-buffer ()
  "Debug helper function.
Verify that CRDT IDs in a document follows ascending order."
  (let* ((pos (point-min))
         (id (crdt--get-starting-id pos)))
    (cl-block nil
      (while t
        (let* ((next-pos (next-single-property-change pos 'crdt-id))
               (next-id (if (< next-pos (point-max))
                            (crdt--get-starting-id next-pos)
                          (cl-return)))
               (prev-id (substring id)))
          (crdt--set-id-offset id (+ (- next-pos pos) (crdt--id-offset id)))
          (unless (string< prev-id next-id)
            (error "Not monotonic!"))
          (setq pos next-pos)
          (setq id next-id))))))

;;; Network protocol

(defun crdt--format-message (args)
  "Serialize ARGS (which should be a list) into a string.
Return the string."
  (let ((print-level nil)
        (print-length nil))
    (prin1-to-string args)))

(cl-defun crdt--readable-encode (object &optional (no-properties t))
  "Return an object ``similar'' to OBJECT at best effort.
If NO-PROPERTIES is non-nil,
omit text properties of any strings in the returned object.
The returned object has a printed representation that can be read back.
The symbol CRDT-EVAL is used as an special marker in the encoding
and the behavior is undefined if OBJECT itself contains this symbol."
  (cl-typecase object
    (string (if no-properties (substring-no-properties object) object))
    ((or symbol number character) object)
    (vector (cl-map 'vector #'crdt--readable-encode object))
    (cons (cons (crdt--readable-encode (car object)) (crdt--readable-encode (cdr object))))
    (buffer (list 'crdt-eval 'buffer
                  (buffer-local-value 'crdt--buffer-network-name object)))
    (t (list 'crdt-eval 'unreadable
             (prin1-to-string object)))))

(defun crdt--readable-decode (object)
  "Reconstruct the original object from CRDT--READABLE-ENCODEd OBJECT at best effort."
  (cl-typecase object
    (cons (if (eq (car object) 'crdt-eval)
              (cl-case (cadr object)
                ((buffer) (crdt--with-buffer-name (caddr object) (current-buffer)))
                ((unreadable) (caddr object)))
            (cons (crdt--readable-decode (car object)) (crdt--readable-decode (cdr object)))))
    (vector (cl-map 'vector #'crdt--readable-decode object))
    (t object)))

(defsubst crdt--log-send-network-traffic (message-string)
  (when crdt--log-network-traffic
    (message "Send %s" message-string)))

(cl-defun crdt--broadcast-maybe (message-string &optional (without t))
  "Broadcast or send MESSAGE-STRING.
If (CRDT--SESSION-NETWORK-PROCESS CRDT--SESSION) is a server
process, broadcast MESSAGE-STRING to clients except the one of
which CLIENT-ID property is EQ to WITHOUT.
If (CRDT--SESSION-NETWORK-PROCESS CRDT--SESSION) is a client
process, send MESSAGE-STRING to server when WITHOUT is non-nil."
  (if (process-contact (crdt--session-network-process crdt--session) :server)
      (dolist (client (crdt--session-network-clients crdt--session))
        (when (and (eq (process-status client) 'open)
                   (not (eq (process-get client 'client-id) without)))
          (crdt--log-send-network-traffic message-string)
          (process-send-string client message-string)
          ;; (run-at-time 1 nil #'process-send-string client message-string)
          ;; ^ quick dirty way to simulate network latency, for debugging
          ))
    (when without
      (crdt--log-send-network-traffic message-string)
      (process-send-string (crdt--session-network-process crdt--session) message-string)
      ;; (run-at-time 1 nil #'process-send-string (crdt--session-network-process crdt--session) message-string)
      )))

(defvar crdt--message-handler-table (make-hash-table)
  "Map CRDT message type to handler function.")

(cl-defmacro define-crdt-message-handler (type arglist &body body)
  "Define a crdt message handler.
Define a function CRDT--HANDLE-MESSAGE-[TYPE] with ARGLIST and BODY and
use it to handle message TYPE."
  (declare (debug
            (&define name cl-lambda-list cl-declarations-or-string def-body))
           (doc-string 3)
           (indent 2))
  (let ((function-name (intern (concat "crdt--handle-message-" (symbol-name type)))))
    `(progn
       (cl-defun ,function-name ,arglist ,@body)
       (puthash ',type ',function-name crdt--message-handler-table))))

(defvar crdt--message-string nil
  "Bound to the string representation of the message inside message handler.
So that we don't need to convert MESSAGE to string again
when we need to broadcast it.")

(define-error 'crdt-unrecognized-message "Unhandled crdt-unrecognized-message.")

(defsubst crdt-process-message (message string)
  (let ((crdt--message-string string))
    (let ((handler (gethash (car message) crdt--message-handler-table)))
      (if handler
          (apply handler (cdr message))
        (message "Unrecognized message %S from %s:%s."
                 message (process-contact crdt--process :host) (process-contact crdt--process :service))
        (signal 'crdt-unrecognized-message nil)))))

(defsubst crdt-process-message-1 (message)
  (crdt-process-message message (crdt--format-message message)))

(defsubst crdt--overlay-add-message (id clock species front-advance rear-advance beg end)
  "Create an overlay-add message to be sent to peers.
The overlay is generated at site with ID and logical CLOCK.
The overlay is categorized as SPECIES.
The overlay is FRONT-ADVANCE and REAR-ADVANCE, and lies between BEG and END."
  `(overlay-add ,crdt--buffer-network-name ,id ,clock
                ,species ,front-advance ,rear-advance
                ,beg ,(if front-advance
                          (crdt--get-id beg)
                        (crdt--get-id (1- beg)))
                ,end ,(if rear-advance
                          (crdt--get-id end)
                        (crdt--get-id (1- end)))))

(defsubst crdt--generate-challenge ()
  "Generate a challenge string for authentication."
  (apply #'unibyte-string (cl-loop for i below 32 collect (random 256))))

(defsubst crdt--sync-buffer-to-client (buffer)
  "Send messages to a client about the full state of BUFFER.
CRDT--PROCESS should be bound to the network process for the client connection."
  (with-current-buffer buffer
    (save-restriction
      (widen)
      (process-send-string crdt--process
                           (crdt--format-message
                            `(sync
                              ,crdt--buffer-network-name
                              ,@ (crdt--dump-ids (point-min) (point-max) nil nil t))))
      (process-send-string crdt--process (crdt--format-message `(ready ,crdt--buffer-network-name ,major-mode)))

      ;; synchronize cursor
      (maphash (lambda (user-id ov-pair)
                 (cl-destructuring-bind (cursor-ov . region-ov) ov-pair
                   (let* ((point (overlay-start cursor-ov))
                          (region-beg (overlay-start region-ov))
                          (region-end (overlay-end region-ov))
                          (mark (if (eq point region-beg)
                                    (unless (eq point region-end) region-end)
                                  region-beg)))
                     (process-send-string crdt--process
                                          (crdt--format-message
                                           `(cursor ,crdt--buffer-network-name ,user-id
                                                    ,point ,(crdt--get-id point)
                                                    ,mark ,(when mark (crdt--get-id mark))))))))
               crdt--pseudo-cursor-table)
      (process-send-string crdt--process (crdt--format-message (crdt--local-cursor nil)))

      ;; synchronize tracked overlay
      (maphash (lambda (k ov)
                 (let ((meta (overlay-get ov 'crdt-meta)))
                   (process-send-string
                    crdt--process
                    (crdt--format-message (crdt--overlay-add-message
                                           (car k) (cdr k)
                                           (crdt--overlay-metadata-species meta)
                                           (crdt--overlay-metadata-front-advance meta)
                                           (crdt--overlay-metadata-rear-advance meta)
                                           (overlay-start ov)
                                           (overlay-end ov))))
                   (cl-loop for (prop value) on (crdt--overlay-metadata-plist meta) by #'cddr
                         do (process-send-string
                             crdt--process
                             (crdt--format-message `(overlay-put ,crdt--buffer-network-name
                                                                 ,(car k) ,(cdr k) ,prop ,value))))))
               crdt--overlay-table)

      (crdt--send-process-mark-maybe nil)
      (crdt--send-variables-maybe nil))))

(defun crdt--greet-client ()
  "Send initial information when a client connects.
Those information include the assigned USER-ID, buffer list,
and contact data of other users.
CRDT--PROCESS should be bound to The network process for the client connection."
  (let ((crdt--session (process-get crdt--process 'crdt-session)))
    (cl-pushnew crdt--process (crdt--session-network-clients crdt--session))
    (let ((client-id (process-get crdt--process 'client-id)))
      (unless client-id
        (process-put crdt--process 'client-id (crdt--session-next-user-id crdt--session))
        (setq client-id (crdt--session-next-user-id crdt--session))
        (process-send-string crdt--process (crdt--format-message
                                      `(login ,client-id)))
        (cl-incf (crdt--session-next-user-id crdt--session)))
      (process-send-string crdt--process (crdt--format-message
                                          `(add ,@(hash-table-keys (crdt--session-buffer-table crdt--session)))))
      ;; synchronize contact
      (maphash (lambda (k v)
                 (dolist (slot '(name focus))
                   (process-send-string
                    crdt--process
                    (crdt--format-message
                     `(contact ,k ,slot ,(cl-struct-slot-value 'crdt--contact-metadata slot v))))))
               (crdt--session-contact-table crdt--session))
      ;; send fcaps
      (dolist (fcap (crdt--compute-user-fcaps
                        (crdt--session-permissions crdt--session)
                        client-id))
        (setq fcap (crdt--intern-fcap fcap))
        (process-send-string crdt--process
                             (crdt--format-message
                              `(fcap ,(crdt-local-fcap-name fcap)
                                     ,(crdt-local-fcap-nonce fcap)
                                     ,(crdt-local-fcap-in-states fcap)
                                     ,(crdt-local-fcap-out-states fcap)
                                     ,@ (interactive-form (crdt-local-fcap-proxy fcap)))))))))

(define-crdt-message-handler insert (buffer-name user-id crdt-id position-hint content)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (crdt--remote-insert crdt-id user-id position-hint content)))
  (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))

(define-crdt-message-handler delete (buffer-name _user-id position-hint . id-pairs)
  (mapc (lambda (p) (rplaca (cdr p) (cadr p))) id-pairs)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (crdt--remote-delete position-hint id-pairs)))
  (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))

(define-crdt-message-handler cursor
    (buffer-name user-id point-position-hint point-crdt-id mark-position-hint mark-crdt-id)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (crdt--remote-cursor user-id point-position-hint point-crdt-id
                             mark-position-hint mark-crdt-id)))
  (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))

(define-crdt-message-handler get (buffer-name)
  (let ((buffer (gethash buffer-name (crdt--session-buffer-table crdt--session))))
    (if (and buffer (buffer-live-p buffer))
        (crdt--sync-buffer-to-client buffer)
      (process-send-string crdt--process (crdt--format-message `(remove ,buffer-name))))))

(define-crdt-message-handler sync (buffer-name . ids)
  (unless (crdt--server-p)             ; server shouldn't receive this
    (crdt--with-buffer-name buffer-name
      (let ((crdt--inhibit-update t)
            (inhibit-read-only t))
        (unless crdt--buffer-sync-callback
          ;; try to get to the same position after sync,
          ;; if crdt--buffer-sync-callback is not set yet
          (let ((pos (point)))
            (setq crdt--buffer-sync-callback
                  (lambda ()
                    (goto-char
                     (max (min pos (point-max))
                          (point-min)))))))
        (erase-buffer)
        (crdt--load-ids ids)))
    (crdt--refresh-buffers-maybe)))

(define-crdt-message-handler ready (buffer-name mode)
  (crdt--with-buffer-name buffer-name
    (unless (fboundp mode)
      (when (get mode 'crdt-autoload)
        (require (get mode 'crdt-autoload) nil t)))
    (if (fboundp mode)
        (unless (eq major-mode mode)
          (if (not (string-match-p "-mode$" (symbol-name mode))) ; An ad-hoc security check...
              (warn "Remote session uses mode %s, but I refuse to turn it on because it doesn't look like a mode." mode)
            (funcall mode)
            (crdt-mode)))
      (warn "Remote session uses mode %s, but not available locally." mode))
    (unless (crdt--server-p)
      (when (gethash 'crdt-get-write-access (crdt--session-remote-fcap-table crdt--session))
        (read-only-mode -1))
      (when crdt--buffer-sync-callback
        (funcall crdt--buffer-sync-callback)
        (setq crdt--buffer-sync-callback nil)))))

(define-crdt-message-handler error (buffer-name &rest err)
  (unless (crdt--server-p)
    (if buffer-name
        (crdt--with-buffer-name buffer-name
          (message "Server side error %s." err)
          (crdt--recover))
      (cl-block nil
        (message "Server side error %s." err)
        (when (eq (car err) 'version)
          (if (version< crdt-protocol-version (cadr err))
              (warn "Server uses newer crdt.el protocol (%s>%s). Please update your crdt.el to connect."
                    (cadr err) crdt-protocol-version)
            (warn "Server uses older crdt.el protocol (%s<%s). Please ask to update server."
                  (cadr err) crdt-protocol-version)))
        (crdt-disconnect)))))

(define-crdt-message-handler add (&rest buffer-names)
  (dolist (buffer-name buffer-names)
    (unless (gethash buffer-name (crdt--session-buffer-table crdt--session))
      (puthash buffer-name nil (crdt--session-buffer-table crdt--session)))
    (crdt--refresh-buffers-maybe)))

(define-crdt-message-handler remove (&rest buffer-names)
  (let ((notify-names
         (cl-remove-if-not
          (lambda (buffer-name)
            (gethash buffer-name (crdt--session-buffer-table crdt--session)))
          buffer-names)))
    (when notify-names
      (warn "Server stopped sharing %s."
            (mapconcat #'identity buffer-names ", "))))
  (let ((session crdt--session))
    (dolist (buffer-name buffer-names)
            (let ((buffer (gethash buffer-name (crdt--session-buffer-table crdt--session))))
              (remhash buffer-name (crdt--session-buffer-table crdt--session))
              (when buffer
                (when (buffer-live-p buffer)
                  (with-current-buffer buffer
                    (crdt-mode 0)
                    (setq-local crdt--session nil))))))
    (let ((crdt--session session)) ; hack to avoid crdt--session (somehow) get set to nil
      ;; update focused buffer
      (maphash (lambda (_k v)
                 (when (member (crdt--contact-metadata-focus v) buffer-names)
                   (setf (crdt--contact-metadata-focus v) nil)))
               (crdt--session-contact-table crdt--session))
      (crdt--broadcast-maybe crdt--message-string (when crdt--process (crdt--client-id)))
      (crdt--refresh-users-maybe))))

(define-crdt-message-handler login (id)
  (setf (crdt--session-local-id crdt--session) id)
  (let ((metadata (gethash nil (crdt--session-contact-table crdt--session))))
    (when metadata
      (remhash nil (crdt--session-contact-table crdt--session))
      (process-send-string
       crdt--process
       (crdt--format-message
        `(contact ,id name ,(crdt--contact-metadata-name metadata))))
      (puthash id metadata (crdt--session-contact-table crdt--session))))
  (crdt--refresh-sessions-maybe))

(define-crdt-message-handler challenge (hash)
  (unless (crdt--server-p)             ; server shouldn't receive this
    (message nil)
    (let ((password (read-passwd
                     (format "Password for %s:%s: "
                             (process-contact (crdt--session-network-process crdt--session) :host)
                             (process-contact (crdt--session-network-process crdt--session) :service)))))
      (crdt--broadcast-maybe (crdt--format-message
                              `(hello ,crdt-protocol-version
                                      ,(gnutls-hash-mac 'SHA1 password hash)))))))

(define-crdt-message-handler contact (user-id slot value)
  (when (and (crdt--server-p) (not (= user-id (crdt--client-id))))
    (signal 'crdt-no-permission "User ID mismatch in CONTACT message"))
  (cl-symbol-macrolet ((metadata (gethash user-id (crdt--session-contact-table crdt--session))))
    (unless metadata (setf metadata (crdt--make-contact-metadata)))
    (setf (cl-struct-slot-value 'crdt--contact-metadata slot metadata) value))
  (when (eq user-id (crdt--session-follow-user-id crdt--session))
    (crdt--with-buffer-name-pull (value)
      (switch-to-buffer (current-buffer))
      (let ((ov-pair (gethash user-id crdt--pseudo-cursor-table)))
        (when ov-pair (goto-char (overlay-start (car ov-pair)))))))
  (crdt--refresh-users-maybe)
  (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))

(define-crdt-message-handler leave (user-id)
  (if (and (crdt--server-p) (eq (process-status crdt--process) 'open))
    ;; we must check that process status is open to avoid infinite
    ;; recursion when the handler is called inside client process sentinel
      (progn
        (unless (= user-id (crdt--client-id))
          (signal 'crdt-no-permission "User ID mismatch in LEAVE message"))
        (delete-process crdt--process))
    (when (eq user-id (crdt--session-follow-user-id crdt--session))
      (crdt-stop-follow))
    (remhash user-id (crdt--session-contact-table crdt--session))
    (crdt--refresh-users-maybe)
    (crdt--broadcast-maybe crdt--message-string (crdt--client-id))))

(defun crdt--network-filter (process string)
  "Network filter function for CRDT network processes.
Handle received STRING from PROCESS."
  (unless (and (process-buffer process)
               (buffer-live-p (process-buffer process)))
    (set-process-buffer process (generate-new-buffer " *crdt-server*"))
    (with-current-buffer (process-buffer process)
      (set-marker (process-mark process) 1)))
  (with-current-buffer (process-buffer process)
    (unless crdt--session
      (setq crdt--session (process-get process 'crdt-session)))
    (when (> (length string) 0)
      (setf (crdt--session-roger-p crdt--session) t))
    (save-excursion
      (goto-char (process-mark process))
      (insert string)
      (set-marker (process-mark process) (point))
      (goto-char (point-min))
      (let (message string start (crdt--process process))
        (while (setq start (point)
                     message (ignore-errors (read (current-buffer))))
          (when crdt--log-network-traffic
            (print message))
          (setq string (buffer-substring-no-properties start (point)))
          (delete-region (point-min) (point))
          (goto-char (point-min))
          (condition-case err
              (if (or (not (crdt--server-p)) (process-get process 'authenticated))
                  (let ((crdt--inhibit-update t))
                    (crdt-process-message message string))
                (cl-block nil
                  (when (eq (car message) 'hello)
                    (cl-destructuring-bind (protocol-version &optional response) (cdr message)
                      (when (version< protocol-version crdt-protocol-version)
                        (process-send-string process
                                             (crdt--format-message `(error nil version ,crdt-protocol-version)))
                        (cl-return))
                      (when (or (not (process-get process 'password)) ; server password is empty
                                (and response (string-equal response (process-get process 'challenge))))
                        (process-put process 'authenticated t)
                        (crdt--greet-client)
                        (cl-return))))
                  (let ((challenge (crdt--generate-challenge)))
                    (process-put process 'challenge
                                 (gnutls-hash-mac 'SHA1 (substring (process-get process 'password)) challenge))
                    (process-send-string process (crdt--format-message `(challenge ,challenge))))))
            ((crdt-unrecognized-message invalid-read-syntax)
             (warn "%s error when processing message %s from %s:%s, disconnecting." err message
                      (process-contact process :host) (process-contact process :service))
             (if (crdt--server-p)
                 (delete-process process)
               (crdt--stop-session crdt--session)))))))))

(defun crdt--server-process-sentinel (client _message)
  (let ((crdt--session (process-get client 'crdt-session)))
    (unless (or (process-contact client :server) ; it's actually server itself
                (eq (process-status client) 'open))
      ;; client disconnected
      (setf (crdt--session-network-clients crdt--session)
            (delq client (crdt--session-network-clients crdt--session)))
      ;; generate a clear cursor message and a clear contact message
      (let* ((client-id (process-get client 'client-id))
             (clear-contact-message `(leave ,client-id)))
        (when client-id ; we only do stuff if actually a CRDT client disconnect, not some spider/scanner etc
          (let ((crdt--process client))
            (crdt-process-message-1 clear-contact-message))
          (maphash
           (lambda (k _)
             (let ((crdt--process client))
               (crdt-process-message-1 `(cursor ,k ,client-id 1 nil 1 nil))))
           (crdt--session-buffer-table crdt--session))))
      (when (process-buffer client) (kill-buffer (process-buffer client))))))

(defun crdt--client-process-sentinel (process _message)
  (unless (eq (process-status process) 'open)
    (let ((session (process-get process 'crdt-session)))
      (when session
        (if (and (not (crdt--session-roger-p session))
                 (process-get process 'crdt--downgrade-continuation))
            ;; This should only happens when we are in the middle of TLS handshake
            (funcall (process-get process 'crdt--downgrade-continuation))
          (when (process-get process 'tuntox-process)
            (process-send-string
             process
             (crdt--format-message `(leave ,(crdt--session-local-id session)))))
          (crdt--stop-session session))))))

;;; UI commands

(defvar crdt--ephemeral-advices nil)

(defun crdt--call-with-ephemeral-advice (symbol around-advice thunk)
  (let ((wrapped-advice
         (lambda (orig-func &rest args)
           (if (memq symbol crdt--ephemeral-advices)
               (apply around-advice orig-func args)
             (apply orig-func args)))))
    (unwind-protect
         (if (memq symbol crdt--ephemeral-advices)
             (funcall thunk)
           (let ((crdt--ephemeral-advices (cons symbol crdt--ephemeral-advices)))
             (advice-add symbol :around wrapped-advice)
             (funcall thunk)))
      (unless (memq symbol crdt--ephemeral-advices)
        (advice-remove symbol wrapped-advice)))))

(defvar crdt-read-settings-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "<tab>") #'forms-next-field)
    (define-key map (kbd "<backtab>") #'forms-prev-field)
    (define-key map "\C-m" #'exit-recursive-edit)
    (define-key map "\C-g" #'abort-recursive-edit)
    (define-key map "\M-n" 'forms-next-record)
    (define-key map "\M-p" 'forms-prev-record)
    (define-key map (kbd "M->") 'forms-first-record)
    (define-key map (kbd "M-<") 'forms-last-record)
    (define-key map [remap forms-insert-record] 'ignore)
    ;; (define-key map [remap forms-jump-record] 'ignore)
    (define-key map [remap forms-exit] 'ignore)
    map))

(defun crdt-read-settings (buffer-name settings-list)
  "Display a form in a buffer for editing some settings.
Use the buffer with BUFFER-NAME to display the form (create if
not exist).  Use the buffer with BUFFER-NAME prepended by a space
to store history (create if not exist).
SETTINGS-LIST should be a list with elements of the form
 (PROMPT DEFAULT-CONTENT &optional FUNCTION).  FUNCTION, if
non-nil, is called on the user entered string to get the settings
value.  Returns a list of settings values correpsonding to
SETTINGS-LIST."
  (with-current-buffer (get-buffer-create buffer-name)
    (let ((enable-local-eval t)
          (data-buffer (get-buffer-create (concat " " buffer-name)))
          (default-content-string
           (cl-loop for entry in settings-list
                 concat (cadr entry)
                 concat "\t")))
      (aset default-content-string (1- (length default-content-string)) ?\n)
      (let ((standard-output (current-buffer)))
        (prin1
         `(setq forms-file t
                forms-number-of-fields ,(length settings-list)
                forms-format-list
                '(,(let ((overriding-local-map crdt-read-settings-map))
                     (substitute-command-keys
                      crdt-read-settings-help-string))
                  ,@(cl-loop for i from 1
                          for entry in settings-list
                          nconc (list (car entry) i "\n"))))))
      (crdt--call-with-ephemeral-advice
       'forms--help 'ignore
       (lambda ()
         (crdt--call-with-ephemeral-advice
          'find-file-noselect
          (lambda (orig-func file)
            (if (eq file t)
                (with-current-buffer data-buffer
                  (save-excursion
                    (goto-char (point-max))
                    (forward-line -1)
                    (unless (looking-at-p (regexp-quote default-content-string))
                      (goto-char (point-max))
                      (insert default-content-string)))
                  (current-buffer))
              (funcall orig-func file)))
          #'forms-mode)))
      (unwind-protect
           (progn
             (use-local-map crdt-read-settings-map)
             (display-buffer (current-buffer)
                             '(display-buffer-below-selected
                               (window-height . fit-window-to-buffer)))
             (select-window (get-buffer-window (current-buffer)))
             (forms-last-record)
             (let ((debug-on-error nil))
               ;; avoid reaching start/end of history cause recursive edit to abort
               (recursive-edit))
             (forms--update)
             (cl-mapcar (lambda (entry data)
                          (funcall (or (caddr entry) #'identity) data))
                        settings-list forms--the-record-list))
        (kill-buffer (current-buffer))
        (unless (< (length (window-list)) 2)
          (delete-window (get-buffer-window (current-buffer))))))))

(defun crdt--generate-new-name (name names format)
  "Return a string not in NAMES based on NAME and FORMAT."
  (if (member name names)
      (cl-loop for i from 1
            for new-name = (format format name (number-to-string i))
            unless (member new-name names)
            do (cl-return new-name))
    name))

(cl-defun crdt--share-buffer
    (buffer &optional (session crdt--session) (network-name (buffer-name buffer)))
  "Add BUFFER to CRDT SESSION with NETWORK-NAME.
Possibly add a suffix to NETWORK-NAME to avoid duplicated network names.
Return BUFFER."
  (cl-flet ((content-message ()
              (save-excursion
                (save-restriction
                  (widen)
                  (let ((crdt--inhibit-update t))
                    (with-silent-modifications
                      (crdt--local-insert (point-min) (point-max))))))))
    (let ((new-name (crdt--generate-new-name
                     network-name
                     (hash-table-keys (crdt--session-buffer-table session))
                     "%s<%s>")))
      (if (process-contact (crdt--session-network-process session) :server)
          (with-current-buffer buffer
            (setq crdt--session session)
            (puthash new-name buffer (crdt--session-buffer-table crdt--session))
            (setq crdt--buffer-network-name new-name
                  crdt--site-id 0 crdt--site-id-table (make-hash-table))
            (crdt-mode)
            (content-message)
            (crdt--broadcast-maybe
             (crdt--format-message `(add ,crdt--buffer-network-name))
             crdt--remote-call-spawn-user-id)
            (crdt--refresh-buffers-maybe)
            (crdt--refresh-sessions-maybe)
            buffer)
        (with-current-buffer buffer
          (setq crdt--buffer-network-name new-name
                crdt--session session)
          (crdt-remote-apply (crdt-get-fcap 'crdt-get-buffer-create) (list new-name))

          (setq crdt--site-id (crdt-remote-apply (crdt-get-fcap 'crdt-get-write-access) nil))
          (puthash new-name buffer (crdt--session-buffer-table crdt--session))
          (crdt-mode)
          (dolist (message (content-message))
            (crdt--broadcast-maybe (crdt--format-message message)))
          (crdt--broadcast-maybe (crdt--format-message `(ready ,crdt--buffer-network-name ,major-mode))))))))

(defun crdt--settings-make-ensure-type (type-predicate)
  (lambda (string)
    (let ((result (car (read-from-string string))))
      (unless (funcall type-predicate result)
        (signal 'wrong-type-argument (list type-predicate result)))
      result)))

(defun crdt--settings-make-ensure-nonempty (default)
  (lambda (string)
   (if (and string (> (length string) 0))
       string default)))

;;;###autoload
(defun crdt-share-buffer (session-name)
  "Share the current buffer in the CRDT session with name SESSION-NAME.
Create a new one if such a CRDT session doesn't exist."
  (interactive
   (progn
     (when (and crdt-mode crdt--session)
       (error "Current buffer is already shared in a CRDT session"))
     (list (let* ((session-names (mapcar #'crdt--session-urlstr crdt--session-list))
                  (session-name (and session-names
                                   (completing-read "Choose a session (create if not exist): " session-names))))
             session-name))))
  (let ((session (crdt--get-session session-name)))
    (crdt--share-buffer
     (current-buffer)
     (or session
         (apply #'crdt-new-session
                (crdt-read-settings
                 (format "*Settings for new CRDT session*")
                 `(("Port: " "6530" ,(crdt--settings-make-ensure-type 'numberp))
                   ("Secure Port: " ,(if crdt-use-stunnel "6540" "--")
                                    ,(when crdt-use-stunnel (crdt--settings-make-ensure-type 'numberp)))
                   ("Password: " "")
                   ("Display Name: " ,crdt-default-name)
                   ("Command Functions: "
                    ,(prin1-to-string crdt-default-session-permissions)
                    ,(crdt--settings-make-ensure-type 'listp)))))))))

(cl-defun crdt-stop-share-buffer (&optional (session crdt--session)
                                 (network-name crdt--buffer-network-name))
  "Stop sharing buffer with NETWORK-NAME in SESSION."
  (interactive (let ((session (crdt--read-session-maybe 'server)))
                 (list session (crdt--read-buffer-maybe session))))
  (if session
      (if (crdt--server-p)
          (let ((remove-message `(remove ,network-name)))
            (crdt-process-message-1 remove-message))
        (message "Only server can stop sharing a buffer."))
    (message "Not a CRDT shared buffer.")))

(defun crdt-generate-certificate (save-path &optional certtool-executable log-file)
  "Generate a self-signed certificate with private key.
Store the .pem file to SAVE-PATH.  If CERTTOOL-EXECUTABLE is
provided, it should be a path to a GnuTLS executable, which will
be used.  Otherwise, search for gnutls-certtool, then certtool,
in (EXEC-PATH).  Write diagnostic outputs to LOG-FILE.  If
LOG-FILE is nil, append .log to SAVE-PATH and use that instead."
  (setq save-path (expand-file-name save-path))
  (setq log-file
        (if log-file (expand-file-name log-file)
          (concat save-path ".log")))
  (unless certtool-executable
    (setq certtool-executable
          (or (locate-file "gnutls-certtool" (exec-path) exec-suffixes 1)
              (locate-file "certtool" (exec-path) exec-suffixes 1))))
  (unless certtool-executable
    (signal 'file-error "Cannot locate GnuTLS certificate tool executable."))
  (with-temp-file save-path
    (let ((save-buffer (current-buffer)))
      (unless (= 0 (call-process certtool-executable nil (list save-buffer log-file) nil "-p"))
        (error "Failed to generate private key"))
      (write-region nil nil save-path)
      (with-temp-buffer
        (insert "tls_www_server")
        (unless (= 0 (call-process-region
                      nil nil certtool-executable nil (list save-buffer log-file) nil
                      "-s" "--load-privkey" save-path "--template=/dev/stdin"))
          (error "Failed to generate certificate"))))))

(defun crdt-start-stunnel (port secure-port)
  "Start a stunnel proxy that forwards SECURE-PORT to PORT.
Return the stunnel proxy process."
  (unless (file-exists-p crdt-tls-certificate)
    (if (yes-or-no-p (format "%s does not exist. Generate a self-signing certificate? "
                             crdt-tls-certificate))
        (crdt-generate-certificate crdt-tls-certificate)
      (error "TLS certificate %s does not exist" crdt-tls-certificate)))
  (let ((stunnel-process
         (make-process :name "Stunnel Proxy"
                       :buffer (generate-new-buffer "*Stunnel Proxy*")
                       :command `(,crdt-stunnel-executable "/dev/stdin"))))
    (display-buffer (process-buffer stunnel-process))
    (process-send-string stunnel-process
                         (format "foreground=yes\ncert=%s\nkey=%s\n[ein]\naccept=%d\nconnect=%d\n"
                                 (expand-file-name crdt-tls-certificate)
                                 (expand-file-name crdt-tls-private-key)
                                 secure-port port))
    (process-send-eof stunnel-process)
    stunnel-process))

(defun crdt-new-session
    (port secure-port password display-name permissions)
  "Start a new CRDT session on PORT.
When CRDT-USE-STUNNEL is non nil, also start a stunnel proxy on SECURE-PORT,
otherwise SECURE-PORT is ignored.
Setup up the server with PASSWORD and assign this Emacs DISPLAY-NAME.
PERMISSIONS is a list that describes policies
for public session-scoped functionss.
Each element should be one of
- a function, which should return a list of `crdt-local-fcap's when
  called with a single argument USER-ID.
  The returned list of fcaps is made accessible
  to the user with USER-ID in every buffer.
- a symbol, which has a list of `crdt-local-fcap's as its value.
  These fcaps are made accessible to every user, in every buffer.
- a list of `crdt-local-fcap's
  These fcaps are made accessible to every user, in every buffer."
  (let* ((network-process (make-network-process
                           :name "CRDT Server"
                           :server t
                           :host "0.0.0.0"
                           :service port
                           :filter #'crdt--network-filter
                           :sentinel #'crdt--server-process-sentinel
                           :coding 'utf-8))
         (new-session
          (crdt--make-session :local-id 0
                              :local-clock 0
                              :next-user-id 1
                              :local-name display-name
                              :host "localhost" :service port
                              :urlstr (format "localhost:%s" port)
                              :network-process network-process
                              :permissions permissions))
         (tuntox-p (or (eq crdt-use-tuntox t)
                       (and (eq crdt-use-tuntox 'confirm)
                            (yes-or-no-p "Start a tuntox proxy for this session? ")))))
    (process-put network-process 'crdt-session new-session)
    (push new-session crdt--session-list)
    (if tuntox-p ; TODO: factor this out like `crdt-start-stunnel'
        (let* ((password-p (and password (> (length password) 0)))
               (proxy-process
                (make-process :name "Tuntox Proxy"
                              :buffer (generate-new-buffer "*Tuntox Proxy*")
                              :command
                              `(,crdt-tuntox-executable
                                "-C" ,(expand-file-name crdt-tuntox-key-path)
                                "-f" "/dev/stdin" ; do the filtering for safety sake
                                ,@ (when password-p
                                     `("-s" ,password))))))
          (when password-p
            (process-put proxy-process 'password password))
          (display-buffer (process-buffer proxy-process))
          (process-put network-process 'tuntox-process proxy-process)
          (process-send-string proxy-process (format "127.0.0.1:%s\n" port)) ; only allow connection to our port
          (process-send-eof proxy-process))
      (when (and password (> (length password) 0))
        (process-put network-process 'password password)))
    (when crdt-use-stunnel
      (condition-case c
          (process-put network-process 'stunnel-process (crdt-start-stunnel port secure-port))
        (error (warn "Stunnel proxy not started: %s" c))))
    new-session))

(defun crdt--stop-session (session)
  "Kill the CRDT SESSION."
  (interactive (list (crdt--read-session-maybe 'server)))
  (when (if (and crdt-confirm-disconnect
                 (crdt--server-p session)
                 (crdt--session-network-clients session))
            (yes-or-no-p "There are yet connected clients. Stop session? ")
          t)
    (dolist (client (crdt--session-network-clients session))
      (when (process-live-p client)
        (delete-process client))
      (when (process-buffer client)
        (kill-buffer (process-buffer client))))
    (when (crdt--session-user-menu-buffer session)
      (kill-buffer (crdt--session-user-menu-buffer session)))
    (when (crdt--session-buffer-menu-buffer session)
      (kill-buffer (crdt--session-buffer-menu-buffer session)))
    (maphash
     (lambda (_ v)
       (when (and v (buffer-live-p v))
         (with-current-buffer v
           (setq crdt--session nil)
           (crdt-mode 0))))
     (crdt--session-buffer-table session))
    (setq crdt--session-list
          (delq session crdt--session-list))
    (crdt--refresh-sessions-maybe)
    (let* ((process (crdt--session-network-process session))
           (process-buffer (process-buffer process)))
      (delete-process (crdt--session-network-process session))
      (when (and process-buffer (buffer-live-p process-buffer))
        (kill-buffer process-buffer))
      (dolist (proxy-process (list (process-get process 'tuntox-process)
                                   (process-get process 'stunnel-process)))
        (when (and proxy-process (process-live-p proxy-process))
          (interrupt-process proxy-process))))
    (unless (memq this-command '(crdt-disconnect crdt-stop-session crdt--stop-session))
      (warn "CRDT Session %s disconnected." (crdt--session-urlstr session)))))

(defun crdt-stop-session (&optional session)
  "Stop sharing the SESSION.
If SESSION is nil, stop sharing the current session."
  (interactive
   (list (crdt--read-session-maybe 'server)))
  (crdt--stop-session (or session crdt--session)))

(defun crdt-copy-url (&optional session)
  "Copy the url for the SESSION.
Currently this only work if a tuntox proxy is used."
  (interactive
   (list (crdt--read-session-maybe 'server)))
  (let* ((session (or session crdt--session))
         (network-process (crdt--session-network-process session))
         (tuntox-process (process-get network-process 'tuntox-process)))
    (if tuntox-process
        (let ((url-base (format "tuntox://%s:%s"
                                (with-current-buffer (process-buffer tuntox-process)
                                  (save-excursion
                                    (goto-char (point-min))
                                    (search-forward "Using Tox ID: ")
                                    (let ((start (point)))
                                      (end-of-line)
                                      (buffer-substring-no-properties start (point)))))
                                (process-contact network-process :service))))
          (kill-new (if (and crdt-tuntox-password-in-url (process-get tuntox-process 'password))
                        (format "%s?pwd=%s"
                                url-base
                                (process-get tuntox-process 'password))
                      url-base))
          (message "URL copied."))
      (message "No known URL to copy, find out your public IP address yourself!"))))

(defun crdt-disconnect (&optional session)
  "Disconnect from client SESSION.
If SESSION is nil, disconnect from the current session."
  (interactive
   (list (crdt--read-session-maybe 'client)))
  (crdt--stop-session (or session crdt--session)))

(defvar crdt-connect-url-history nil)

;;;###autoload
(defun crdt-connect (url display-name)
  "Connect to a CRDT server running at URL.
Open a new buffer to display the shared content.
Join with DISPLAY-NAME."
  (interactive
   (crdt-read-settings
    "*CRDT Connect Settings*"
    `(("URL: " "" ,(lambda (url)
                     (let (parsed-url)
                       (when (eq (length url) 0)
                         (error "Please input a valid URL"))
                       (setq parsed-url (url-generic-parse-url url))
                       (when (or (not (url-type parsed-url))
                                 (string-equal (url-type parsed-url) "localhost")) ; for ease of local debugging
                         (let ((inferred-protocol
                                (cond ((eq (url-portspec parsed-url) 6530) "ein")
                                      ((eq (url-portspec parsed-url) 6540) "eins")
                                      (crdt-default-tls "eins")
                                      (t "ein"))))
                           (setq parsed-url (url-generic-parse-url (concat inferred-protocol "://" url)))))
                       (when (not (url-portspec parsed-url))
                         (pcase (url-type parsed-url)
                           ("eins" (setf (url-portspec parsed-url) 6540))
                           ("ein" (setf (url-portspec parsed-url) 6530))
                           ("tuntox" (setf (url-portspec parsed-url) 6530))))
                       parsed-url)))
      ("Display Name: " ,crdt-default-name ,(crdt--settings-make-ensure-nonempty crdt-default-name)))))
  (unless (url-p url)
    (when (eq (length url) 0)
      (error "Please input a valid URL"))
    (let ((parsed-url (url-generic-parse-url url)))
      (when (or (not (url-type parsed-url))
                (string-equal (url-type parsed-url) "localhost")) ; for ease of local debugging
        (setq parsed-url (url-generic-parse-url (concat "eins://" url))))
      (setq url parsed-url)))
  (when (not (url-portspec url))
    (pcase (url-type url)
      ("eins" (setf (url-portspec url) 6540))
      ("ein" (setf (url-portspec url) 6530))
      ("tuntox" (setf (url-portspec url) 6530))))
  (let ((url-type (url-type url))
        (new-session (crdt--make-session :local-clock 0 :local-name display-name)))
    (cl-flet ((start-session (&rest process-args)
                (let* ((network-process (apply #'make-network-process
                                               :name "CRDT Client"
                                               :buffer (generate-new-buffer " *crdt-client*")
                                               :filter #'crdt--network-filter
                                               :sentinel #'crdt--client-process-sentinel
                                               :coding 'utf-8
                                               process-args)))
                  (setf (crdt--session-urlstr new-session) (url-recreate-url url)
                        (crdt--session-network-process new-session) network-process)
                  (process-put network-process 'crdt-session new-session)
                  (process-send-string
                   network-process
                   (crdt--format-message
                    `(hello ,crdt-protocol-version)))
                  network-process)))
      (cond ((equal url-type "ein")
             (start-session :host (url-host url) :service (url-portspec url)))
            ((equal url-type "eins")
             (cl-flet ((downgrade ()
                         (let ((old-url-string (url-recreate-url url)))
                           (setf (url-portspec url) 6530 (url-type url) "ein")
                           (warn "Failed to connect to %s, falling back to %s" old-url-string (url-recreate-url url))
                           (start-session :host (url-host url) :service (url-portspec url)))))
               (condition-case c
                   (let ((proc
                          (start-session :host (url-host url) :service (url-portspec url)
                                         :tls-parameters
                                         (cons 'gnutls-x509pki
                                               (gnutls-boot-parameters
                                                :type 'gnutls-x509pki
                                                :hostname (url-host url))))))
                     (when (= (url-portspec url) 6540)
                       (process-put proc 'crdt--downgrade-continuation
                                    (lambda ()
                                      (process-put proc 'crdt--downgrade-continuation nil)
                                      (downgrade))))
                     proc)
                 (file-error
                  (if (= (url-portspec url) 6540)
                      (downgrade)
                    (signal (car c) (cdr c)))))))
            ((equal url-type "tuntox")
             (let ((port (read-from-minibuffer (format "tuntox proxy port (default %s): "
                                                       (1+ (url-portspec url)))
                                               nil nil t nil (format "%s" (1+ (url-portspec url)))))
                   (password (or (when (url-filename url)
                                   (cadr (split-string (url-filename url) "?pwd=")))
                                 (read-passwd "tuntox password (empty for no password): "))))
               (switch-to-buffer-other-window
                (process-buffer
                 (make-process
                  :name "Tuntox Proxy"
                  :buffer (generate-new-buffer "*Tuntox Proxy*")
                  :command
                  `(,crdt-tuntox-executable
                    "-i" ,(url-host url)
                    "-L" ,(format "%s:127.0.0.1:%s" port (url-portspec url))
                    ,@ (when (> (length password) 0)
                         `("-s" ,password)))
                  :filter
                  (let (initialized)
                    (lambda (proc string)
                      (when (buffer-live-p (process-buffer proc))
                        (with-current-buffer (process-buffer proc)
                          (let ((moving (= (point) (process-mark proc))))
                            (save-excursion
                              (goto-char (process-mark proc))
                              (insert string)
                              (set-marker (process-mark proc) (point))
                              (unless initialized
                                (when (ignore-errors (search-backward "Friend request accepted"))
                                  (setq initialized t)
                                  (process-put (start-session :host "127.0.0.1" :service port)
                                               'tuntox-process proc))))
                            (if moving (goto-char (process-mark proc)))))))))))
               nil))
            (t (error "Unknown protocol \"%s\"" url-type)))
      (push new-session crdt--session-list)
      (let ((crdt--session new-session))
        (crdt-list-buffers))
      new-session)))

;;; overlay tracking

(defvar crdt--inhibit-overlay-advices nil)

(defvar crdt--modifying-overlay-metadata nil)

(defun crdt--enable-overlay-species (species)
  (push species crdt--enabled-overlay-species)
  (when crdt-mode
    (let ((crdt--inhibit-overlay-advices t))
      (maphash (lambda (_ ov)
                 (let ((meta (overlay-get ov 'crdt-meta)))
                   (when (eq species (crdt--overlay-metadata-species meta))
                     (cl-loop for (prop value) on (crdt--overlay-metadata-plist meta) by #'cddr
                           do (overlay-put ov prop value)))))
               crdt--overlay-table))))

(defun crdt--disable-overlay-species (species)
  (setq crdt--enabled-overlay-species (delq species crdt--enabled-overlay-species))
  (when crdt-mode
    (let ((crdt--inhibit-overlay-advices t))
      (maphash (lambda (_ ov)
                 (let ((meta (overlay-get ov 'crdt-meta)))
                   (when (eq species (crdt--overlay-metadata-species meta))
                     (cl-loop for (prop _value) on (crdt--overlay-metadata-plist meta) by #'cddr
                           do (overlay-put ov prop nil)))))
               crdt--overlay-table))))

(defun crdt--make-overlay-advice (orig-fun beg end &optional buffer front-advance rear-advance)
  (let ((new-overlay (funcall orig-fun beg end buffer front-advance rear-advance)))
    ;; should we check if we are in the current buffer?
    (when crdt-mode
      (when crdt--track-overlay-species
        (crdt--broadcast-maybe
         (crdt--format-message
          (crdt--overlay-add-message (crdt--session-local-id crdt--session)
                                     (crdt--session-local-clock crdt--session)
                                     crdt--track-overlay-species front-advance rear-advance
                                     beg end)))
        (let* ((key (cons (crdt--session-local-id crdt--session)
                          (crdt--session-local-clock crdt--session)))
               (meta (crdt--make-overlay-metadata key crdt--track-overlay-species
                                                  front-advance rear-advance nil)))
          (puthash key new-overlay crdt--overlay-table)
          (let ((crdt--inhibit-overlay-advices t)
                (crdt--modifying-overlay-metadata t))
            (overlay-put new-overlay 'crdt-meta meta)))
        (cl-incf (crdt--session-local-clock crdt--session))))
    new-overlay))

(define-crdt-message-handler overlay-add
    (buffer-name user-id logical-clock species
                 front-advance rear-advance start-hint start-id end-hint end-id)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (let* ((crdt--track-overlay-species nil)
               (start (crdt--find-id start-id start-hint front-advance))
               (end (crdt--find-id end-id end-hint rear-advance))
               (new-overlay
                (make-overlay start end nil front-advance rear-advance))
               (key (cons user-id logical-clock))
               (meta (crdt--make-overlay-metadata key species
                                                  front-advance rear-advance nil)))
          (puthash key new-overlay crdt--overlay-table)
          (let ((crdt--inhibit-overlay-advices t)
                (crdt--modifying-overlay-metadata t))
            (overlay-put new-overlay 'crdt-meta meta)))))
  (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))

(defun crdt--move-overlay-advice (orig-fun ov beg end &rest args)
  (when crdt-mode
    (unless crdt--inhibit-overlay-advices
      (let ((meta (overlay-get ov 'crdt-meta)))
        (when meta ;; to be fixed
          (let ((key (crdt--overlay-metadata-lamport-timestamp meta))
                (front-advance (crdt--overlay-metadata-front-advance meta))
                (rear-advance (crdt--overlay-metadata-rear-advance meta)))
            (crdt--broadcast-maybe
             (crdt--format-message
              `(overlay-move ,crdt--buffer-network-name ,(car key) ,(cdr key)
                             ,beg ,(if front-advance
                                       (crdt--get-id beg)
                                     (crdt--get-id (1- beg)))
                             ,end ,(if rear-advance
                                       (crdt--get-id end)
                                     (crdt--get-id (1- end)))))))))))
  (apply orig-fun ov beg end args))

(define-crdt-message-handler overlay-move
    (buffer-name user-id logical-clock
                 start-hint start-id end-hint end-id)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (let* ((key (cons user-id logical-clock))
               (ov (gethash key crdt--overlay-table)))
          (when ov
            (let* ((meta (overlay-get ov 'crdt-meta))
                   (front-advance (crdt--overlay-metadata-front-advance meta))
                   (rear-advance (crdt--overlay-metadata-rear-advance meta))
                   (start (crdt--find-id start-id start-hint front-advance))
                   (end (crdt--find-id end-id end-hint rear-advance)))
              (let ((crdt--inhibit-overlay-advices t))
                (move-overlay ov start end)))))))
  (crdt--broadcast-maybe crdt--message-string nil))

(defun crdt--delete-overlay-advice (orig-fun ov)
  (unless crdt--inhibit-overlay-advices
    (when crdt-mode
      (let ((meta (overlay-get ov 'crdt-meta)))
        (when meta
          (let ((key (crdt--overlay-metadata-lamport-timestamp meta)))
            (remhash key crdt--overlay-table)
            (crdt--broadcast-maybe (crdt--format-message
                                    `(overlay-remove ,crdt--buffer-network-name ,(car key) ,(cdr key)))))))))
  (funcall orig-fun ov))

(define-crdt-message-handler overlay-remove (buffer-name user-id logical-clock)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (let* ((key (cons user-id logical-clock))
               (ov (gethash key crdt--overlay-table)))
          (when ov
            (remhash key crdt--overlay-table)
            (let ((crdt--inhibit-overlay-advices t))
              (delete-overlay ov))))))
  (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))

(defun crdt--overlay-put-advice (orig-fun ov prop value)
  (unless (and (eq prop 'crdt-meta)
               (not crdt--modifying-overlay-metadata))
    (when crdt-mode
      (unless crdt--inhibit-overlay-advices
        (let ((meta (overlay-get ov 'crdt-meta)))
          (when meta
            (setf (crdt--overlay-metadata-plist meta)
                  (plist-put (crdt--overlay-metadata-plist meta) prop value))
            (let* ((key (crdt--overlay-metadata-lamport-timestamp meta))
                   (message (crdt--format-message
                             `(overlay-put ,crdt--buffer-network-name
                                           ,(car key) ,(cdr key) ,prop ,(crdt--readable-encode value)))))
              (crdt--broadcast-maybe message))))))
    (funcall orig-fun ov prop value)))

(define-crdt-message-handler overlay-put (buffer-name user-id logical-clock prop value)
  (setq value (crdt--readable-decode value))
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (let ((ov (gethash (cons user-id logical-clock) crdt--overlay-table)))
          (when ov
            (let ((meta (overlay-get ov 'crdt-meta)))
              (setf (crdt--overlay-metadata-plist meta)
                    (plist-put (crdt--overlay-metadata-plist meta) prop value))
              (when (memq (crdt--overlay-metadata-species meta) crdt--enabled-overlay-species)
                (let ((crdt--inhibit-overlay-advices t))
                  (overlay-put ov prop value))))))))
  (crdt--broadcast-maybe crdt--message-string nil))

(advice-add 'make-overlay :around #'crdt--make-overlay-advice)
(advice-add 'move-overlay :around #'crdt--move-overlay-advice)
(advice-add 'delete-overlay :around #'crdt--delete-overlay-advice)
(advice-add 'overlay-put :around #'crdt--overlay-put-advice)

;;; Auxillary autoload

(defun crdt-register-autoload (mode feature)
  "Register for autoloading FEATURE before CRDT enforce major MODE."
  (put mode 'crdt-autoload feature))

;;; Remote Function

(cl-defun crdt--assemble-state-list (states &optional (session crdt--session))
  (let (result)
    (cl-labels ((collect (entry tail)
                  (unless (assq entry result) (push (cons entry tail) result)))
                (process (entry)
                  (cl-ecase entry
                    ((region) (mapc #'process '(point mark mark-active transient-mark-mode)))
                    ((buffer)
                     (unless (and crdt--session crdt--buffer-network-name) ;; TODO: capability safe
                       (crdt--share-buffer (current-buffer) session))
                     (collect entry (list crdt--buffer-network-name)))
                    ((window)
                     (with-current-buffer (window-buffer (selected-window))
                       (unless (and crdt--session crdt--buffer-network-name) ;; TODO: capability safe
                         (crdt--share-buffer (current-buffer) session))
                       (collect entry (list crdt--buffer-network-name
                                            (window-point (selected-window))))))
                    ((point) (process 'buffer)
                     (collect entry (list (crdt--get-id (point)) (point))))
                    ((mark) (process 'buffer)
                     (collect entry (list (crdt--get-id (mark)) (mark))))
                    ((mark-active transient-mark-mode last-command-event)
                     (collect entry (list (crdt--readable-encode (symbol-value entry))) result)))))
      (mapc #'process states))
    (nreverse result)))

(defun crdt--apply-state-list (state-list)
  (let (vars vals)
    (cl-loop for entry in state-list
          for rest on state-list
          do (cl-case (car entry)
               ((buffer)
                (set-buffer
                 (crdt--with-buffer-name-pull ((cadr entry) :sync t)
                   (current-buffer))))
               ((window)
                (switch-to-buffer
                 (crdt--with-buffer-name-pull ((cadr entry) :sync t)
                   (current-buffer)))
                (set-window-point (selected-window) (caddr entry)))
               ((point) (goto-char (apply #'crdt--id-to-pos (cdr entry))))
               ((mark) (set-mark (apply #'crdt--id-to-pos (cdr entry))))
               ((mark-active transient-mark-mode last-command-event)
                (push (car entry) vars)
                (push (crdt--readable-decode (cadr entry)) vals))))
    (cons vars vals)))

(defun crdt-toggle-override-command ()
  "Toggle whether to override local commands with remote commands."
  (interactive)
  (if crdt-override-command
      (progn
        (setq crdt-override-command nil)
        (dolist (session crdt--session-list)
          (maphash (lambda (fcap-symbol _)
                     (advice-remove fcap-symbol 'crdt-remote-fcap))
                   (crdt--session-remote-fcap-table session))))
      (setq crdt-override-command t)
      (dolist (session crdt--session-list)
        (maphash (lambda (fcap-symbol _)
                   (advice-add fcap-symbol :around (crdt--make-remote-command-advice fcap-symbol)
                               '((name . crdt-remote-fcap))))
                 (crdt--session-remote-fcap-table session))))
  (message "Overriding remote command %s"
           (if crdt-override-command "enabled" "disabled")))

(define-crdt-message-handler fcap
    (fcap-symbol nonce in-states out-states &rest interactive-form)
  (puthash fcap-symbol
           (crdt--make-remote-fcap fcap-symbol nonce in-states out-states interactive-form)
           (crdt--session-remote-fcap-table crdt--session))
  (when crdt-override-command
    (advice-add fcap-symbol :around (crdt--make-remote-command-advice fcap-symbol)
                '((name . crdt-remote-fcap))))
  (cl-case fcap-symbol
    ((crdt-get-write-access)
     (dolist (buffer (hash-table-values (crdt--session-buffer-table crdt--session)))
       (when buffer
         (with-current-buffer buffer (read-only-mode -1)))))))

(define-crdt-message-handler funcall
    (user-id logical-clock spawn-user-id
             state-list nonce fcap-symbol &rest args)
  (let* ((crdt--inhibit-update nil)
         (crdt--remote-call-spawn-user-id spawn-user-id)
         (saved-session crdt--session)
         (return-message
          (condition-case err
              (let ((fcap (gethash fcap-symbol (crdt--session-local-fcap-table crdt--session))))
                (if fcap
                    (if (string-equal nonce (crdt-local-fcap-nonce fcap))
                        (save-mark-and-excursion
                          (save-window-excursion
                            (let ((bindings (crdt--apply-state-list state-list)))
                              (cl-progv (car bindings) (cdr bindings)
                                (prog1 (list t (apply (crdt-local-fcap-proxy fcap) (mapcar #'crdt--readable-decode args)))
                                  (setq state-list (crdt--assemble-state-list (crdt-local-fcap-out-states fcap) saved-session)))))))
                      (list nil 'crdt-invalid-fcap fcap-symbol))
                  (list nil 'crdt-invalid-fcap fcap-symbol)))
            (error (list nil (car err) (crdt--readable-encode (cdr err))))))
         (msg (crdt--format-message
               `(return ,user-id ,logical-clock
                        ,state-list ,@(crdt--readable-encode return-message)))))
    (crdt--log-send-network-traffic msg)
    (process-send-string crdt--process msg)))

(define-crdt-message-handler return (user-id logical-clock state-list success-p &rest return-values)
  (when (eq user-id (crdt--session-local-id crdt--session))
    (puthash logical-clock (cl-list* state-list success-p (crdt--readable-decode return-values))
             crdt--return-message-table)))

(cl-defun crdt-remote-apply
    (remote-fcap args &optional (spawn-user-id (crdt--session-local-id crdt--session)))
  "Remote call REMOTE-FCAP with ARGS.
SPAWN-USER-ID is the user ID where the series of remote calls
originally started."
  (let* ((user-id (crdt--session-local-id crdt--session))
         (logical-clock (crdt--session-local-clock crdt--session))
         (msg (crdt--format-message
               `(funcall ,user-id
                         ,logical-clock ,spawn-user-id
                         ,(crdt--assemble-state-list (crdt-remote-fcap-in-states remote-fcap))
                         ,(crdt-remote-fcap-nonce remote-fcap)
                         ,(crdt-remote-fcap-name remote-fcap)
                         ,@(mapcar #'crdt--readable-encode args)))))
    (crdt--log-send-network-traffic msg)
    (process-send-string (crdt--session-network-process crdt--session) msg)
    (cl-incf (crdt--session-local-clock crdt--session))
    (while (not (gethash logical-clock crdt--return-message-table))
      (accept-process-output (crdt--session-network-process crdt--session)))
    (let ((return-message (gethash logical-clock crdt--return-message-table)))
      (remhash logical-clock crdt--return-message-table)
      (cl-destructuring-bind (state-list success-p &rest return-values) return-message
        (crdt--apply-state-list state-list)
        (if success-p
            (car return-values)
          (signal (car return-values) (cdr return-values)))))))

(defun crdt-remote-call-interactively (remote-fcap spawn-user-id)
  "Remote call REMOTE-FCAP interactively.
SPAWN-USER-ID is the site where the series of remote calls originally started."
  (crdt-remote-apply remote-fcap
                     (advice-eval-interactive-spec (crdt-remote-fcap-interactive-form remote-fcap))
                     spawn-user-id))

(defun crdt-M-x ()
  (interactive)
  (unless crdt--session
    (error "Not a CRDT shared buffer"))
  (let* ((table (crdt--session-remote-fcap-table crdt--session))
         (command-symbol
          (intern-soft
           (completing-read "CRDT Remote Command: "
                            (hash-table-keys table)
                            (lambda (key) (crdt-remote-fcap-interactive-form (gethash key table)))
                            t))))
    (crdt-remote-call-interactively (crdt-get-fcap command-symbol) (crdt--session-local-id crdt--session))))

(defun crdt--make-remote-command-advice (func)
  (eval
   `(cl-macrolet
        ((if-remote (then else)
           `(let (remote-fcap)
             (if (and crdt-override-command
                      (setq remote-fcap (ignore-error crdt-no-permission (crdt-get-fcap ',',func))))
                 ,then ,else))))
      (lambda (orig-func &rest args)
        "Call remote command named ORIG-FUNC conditionally.
Call remote command named ORIG-FUNC with ARGS, when such remote
command is available and CRDT-OVERRIDE-COMMAND is non-nil."
        (interactive
         (lambda (orig-interactive)
           (if-remote
            (advice-eval-interactive-spec (crdt-remote-fcap-interactive-form remote-fcap))
            (advice-eval-interactive-spec orig-interactive))))
        (if-remote
         (crdt-remote-apply remote-fcap args)
         (apply orig-func args))))))

;;; Buffer local variables

(defvar-local crdt-variables nil)

(cl-defun crdt--send-variables-maybe (&optional (incremental t))
  (dolist (var crdt-variables)
    (let ((sender (car (get var 'crdt-variable-scheme))))
      (let ((msg (funcall sender var incremental)))
        (unless (eq msg 'crdt-unchanged)
          (crdt--broadcast-maybe (crdt--format-message
                                  `(var ,crdt--buffer-network-name ,var ,@(crdt--readable-encode msg)))))))))

(define-crdt-message-handler var (buffer-name variable-symbol . args)
  (crdt--with-buffer-name buffer-name
    (funcall (cdr (get variable-symbol 'crdt-variable-scheme))
             variable-symbol args)))

;; Tree diff
;; We use it to provide an incremental variable sender/receiver for general Lisp data structure.
;; Currently we use a naive algorithm which should work reasonably well
;; when there are few shape changes.
;; The naive algorithm also runs in linear time and space.
;; Sophiscated algorithms that computes minimal editing distance are usually much more expensive.

(defsubst crdt--exhaust-thunk (thunk)
  "Keep forcing THUNK until it no longer returns a function.
For poor man's TCO."
  (while (functionp thunk)
    (setq thunk (funcall thunk))))

(defun crdt--diff (old new)
  "Compute tree diff between OLD and NEW.
The result DIFF can be used in (CRDT--NAPPLY-DIFF OLD DIFF) to reproduce NEW."
  (let (result)
    (cl-labels
        ;; we could do a running length encoding of path
        ;; not bothering that for now
        ((process (path old new vindex)
           (cl-typecase old
             (cons (if (consp new)
                       (progn
                         (crdt--exhaust-thunk
                          (process (concat path "a") (car old) (car new) 0))
                         (lambda () (process (concat path "d") (cdr old) (cdr new) 0)))
                     (push (list path new) result)))
             (vector (cond ((not (vectorp new)) (push (list path new) result))
                           ((>= vindex (length old))
                            (unless (= (length old) (length new))
                              (push (list path (substring new vindex)) result)))
                           ((>= vindex (length new))
                            (push (list path nil) result))
                           (t
                            (crdt--exhaust-thunk
                             (process (concat path "a") (aref old vindex) (aref new vindex) 0))
                            (lambda () (process (concat path "d") old new (1+ vindex))))))
             (t (unless (eql old new) (push (list path new) result))))))
      (crdt--exhaust-thunk (process nil old new 0))
      result)))

(defun crdt--napply-diff (old diff)
  "Destructively apply DIFF produced by CRDT--DIFF to OLD."
  ;; we could do them in one pass
  ;; not bothering that for now
  (dolist (update diff)
    (cl-destructuring-bind (path new) update
      (let ((cursor
             (lambda (msg &optional data)
               (cl-ecase msg
                 ((get) old)
                 ((set) (setq old data))
                 ((vindex) 0)))))
        (dotimes (path-index (length path))
          (let ((cursor-data (funcall cursor 'get)))
            (cl-ecase (aref path path-index)
              ((?a)
               (cl-etypecase cursor-data
                 (cons (setq cursor
                             (lambda (msg &optional data)
                               (cl-ecase msg
                                 ((get) (car cursor-data))
                                 ((set) (rplaca cursor-data data))
                                 ((vindex) 0)))))
                 (vector (setq cursor
                               (let ((vindex (funcall cursor 'vindex)))
                                 (lambda (msg &optional data)
                                   (cl-ecase msg
                                     ((get) (aref cursor-data vindex))
                                     ((set) (aset cursor-data vindex data))
                                     ((vindex) 0))))))))
              ((?d)
               (cl-etypecase cursor-data
                 (cons
                  (setq cursor
                        (lambda (msg &optional data)
                          (cl-ecase msg
                            ((get) (cdr cursor-data))
                            ((set) (rplacd cursor-data data))
                            ((vindex) 0)))))
                 (vector (setq cursor
                               (let ((saved-cursor cursor)
                                     (vindex (1+ (funcall cursor 'vindex))))
                                 (lambda (msg &optional data)
                                   (cl-ecase msg
                                     ((get) cursor-data)
                                     ((set)
                                      (lambda ()
                                        (funcall saved-cursor 'set
                                                 (if data
                                                     (vconcat cursor-data data)
                                                   (substring cursor-data 0 vindex)))))
                                     ((vindex) vindex)))))))))))
        (crdt--exhaust-thunk (funcall cursor 'set new)))))
  old)

(defun crdt--diff-server-variable-sender (var incremental)
  (if (crdt--server-p)
      (if incremental
          (let ((diff (crdt--diff (get var 'crdt--diff-cache) (symbol-value var))))
            (if diff
                (progn (put var 'crdt--diff-cache (copy-tree (symbol-value var) t))
                       diff)
              'crdt-unchanged))
        (list (list "" (symbol-value var))))
    'crdt-unchanged))

(defun crdt--diff-server-variable-receiver (var args)
  (unless (crdt--server-p)
      (set var (crdt--napply-diff (symbol-value var) args))))

(defvar crdt-variable-scheme-diff-server (cons #'crdt--diff-server-variable-sender #'crdt--diff-server-variable-receiver))

(defun crdt-register-variable (variable scheme)
  (add-to-list 'crdt-variables variable)
  (put variable 'crdt-variable-scheme
       (if (symbolp scheme) (symbol-value scheme) scheme)))

(defun crdt-unregister-variable (variable)
  (delq variable crdt-variables))

(defun crdt-register-variables (variable-entries)
  (dolist (entry variable-entries)
    (apply #'crdt-register-variable entry)))

(defun crdt-unregister-variables (variable-entries)
  (dolist (entry variable-entries)
    (crdt-unregister-variable (car entry))))

;;; pseudo process

(cl-defstruct (crdt--pseudo-process (:constructor crdt--make-pseudo-process))
  buffer mark)

(defun crdt--pseudo-process-send-string (pseudo-process string)
  (with-current-buffer (crdt--pseudo-process-buffer pseudo-process)
    (crdt--broadcast-maybe (crdt--format-message
                            `(process ,crdt--buffer-network-name ,string)))))

(defun crdt--process-send-string-advice (orig-func process string)
  (if (crdt--pseudo-process-p process)
      (crdt--pseudo-process-send-string process string)
    (funcall orig-func process string)))

(defun crdt--process-send-region-advice (orig-func process start end)
  (if (crdt--pseudo-process-p process)
      (crdt--pseudo-process-send-string process (buffer-substring-no-properties start end))
    (funcall orig-func process start end)))

(defun crdt--get-buffer-process-advice (orig-func buffer)
  (or (funcall orig-func buffer)
      (and buffer
           (setq buffer (get-buffer buffer))
           (buffer-live-p buffer)
           (with-current-buffer buffer
             (or (funcall orig-func buffer)
                 (and crdt--session (not (crdt--server-p))
                      crdt--buffer-pseudo-process))))))

(defun crdt--get-process-advice (orig-func name)
  (if (crdt--pseudo-process-p name)
      name
    (funcall orig-func name)))

(defun crdt--process-mark-advice (orig-func process)
  (if (crdt--pseudo-process-p process)
      (crdt--pseudo-process-mark process)
    (funcall orig-func process)))

(defun crdt--process-name-advice (orig-func process)
  (if (crdt--pseudo-process-p process)
      process
      (funcall orig-func process)))

(define-crdt-message-handler process-mark (buffer-name crdt-id position-hint)
  (crdt--with-buffer-name buffer-name
    (crdt--with-recover
        (save-excursion
          (goto-char (crdt--id-to-pos crdt-id position-hint))
          (let ((buffer-process (get-buffer-process (current-buffer))))
            (if buffer-process
                (progn (set-marker (process-mark buffer-process) (point))
                       (setq crdt--last-process-mark-id crdt-id)
                       (crdt--broadcast-maybe crdt--message-string (crdt--client-id)))
              (unless (crdt--server-p)
                (setq crdt--buffer-pseudo-process
                      (crdt--make-pseudo-process :buffer (current-buffer) :mark (point-marker)))
                (setq crdt--last-process-mark-id crdt-id))))))))

(cl-defun crdt--send-process-mark-maybe (&optional (lazy t))
  (let ((buffer-process (get-buffer-process (current-buffer))))
    (when buffer-process
      (let* ((mark (process-mark buffer-process)))
        (when mark
          (let* ((mark-pos (marker-position mark)))
            (when mark-pos
              (let* ((current-id (crdt--get-id mark-pos)))
                (unless (and lazy (string-equal crdt--last-process-mark-id current-id))
                  (setq crdt--last-process-mark-id current-id)
                  (crdt--broadcast-maybe
                   (crdt--format-message
                    `(process-mark ,crdt--buffer-network-name
                                   ,current-id ,mark-pos))))))))))))

(defun crdt--process-status-advice (orig-func process)
  (if (crdt--pseudo-process-p process)
      'run
    (funcall orig-func process)))

(defun crdt--delete-process-advice (orig-func process)
  (unless (crdt--pseudo-process-p process)
      (funcall orig-func process)))

(defun crdt--process-buffer-advice (orig-func process)
  (if (crdt--pseudo-process-p process)
      (crdt--pseudo-process-buffer process)
    (funcall orig-func process)))

(defun crdt--processp-advice (orig-func object)
  (or (crdt--pseudo-process-p object) (funcall orig-func object)))

(defun crdt--dummy () nil)

(defun crdt--process-sentinel/filter-advice (orig-func process)
  (if (crdt--pseudo-process-p process)
      #'crdt--dummy
    (funcall orig-func process)))

(defun crdt--set-process-sentinel/filter-advice (orig-func process func)
  (if (crdt--pseudo-process-p process)
      nil
      (funcall orig-func process func)))

(defun crdt--process-query-on-exit-flag-advice (orig-func process)
  (unless (crdt--pseudo-process-p process)
    (funcall orig-func process)))

(defun crdt--set-process-query-on-exit-flag-advice (orig-func process)
  (unless (crdt--pseudo-process-p process)
    (funcall orig-func process)))

(defvar crdt--process-advice-alist
  '((process-send-string . crdt--process-send-string-advice)
    (process-send-region . crdt--process-send-region-advice)
    (processp . crdt--processp-advice)
    (get-buffer-process . crdt--get-buffer-process-advice)
    (get-process . crdt--get-process-advice)
    (process-status . crdt--process-status-advice)
    (process-buffer . crdt--process-buffer-advice)
    (process-mark . crdt--process-mark-advice)
    (delete-process . crdt--delete-process-advice)
    (process-name . crdt--process-name-advice)
    (process-sentinel . crdt--process-sentinel/filter-advice)
    (process-filter . crdt--process-sentinel/filter-advice)
    (set-process-sentinel . crdt--set-process-sentinel/filter-advice)
    (set-process-filter . crdt--set-process-sentinel/filter-advice)
    (process-query-on-exit-flag . crdt--process-query-on-exit-flag-advice)
    (process-set-query-on-exit-flag . crdt--set-process-query-on-exit-flag-advice)))

(defun crdt--install-process-advices ()
  "Globally enable advices for simulating remote buffer process.
Those advices seem to possibly interfere with other packages.
Use CRDT--UNINSTALL-PROCESS-ADVICES to disable those advices for the rescue."
  (dolist (pair crdt--process-advice-alist)
    (advice-add (car pair) :around (cdr pair))))

(defun crdt--uninstall-process-advices ()
  "Globally disable advices for simulating remote buffer process."
  (dolist (pair crdt--process-advice-alist)
    (advice-remove (car pair) (cdr pair))))

(crdt--install-process-advices)

(define-crdt-message-handler process (buffer-name string)
  (crdt--with-buffer-name buffer-name
    (process-send-string (get-buffer-process (current-buffer)) string)))

;;; Built-in package integrations

;;;; Org
(define-minor-mode crdt-org-sync-overlay-mode
    "Minor mode to synchronize hidden `org-mode' subtrees."
  :lighter " Sync Org Overlay"
  (if crdt-org-sync-overlay-mode
      (progn
        (save-excursion
          (save-restriction
            (widen)
            ;; heuristic to remove existing org overlays
            (cl-loop for ov in (overlays-in (point-min) (point-max))
                  do (when (memq (overlay-get ov 'invisible)
                                 '(outline org-hide-block))
                       (delete-overlay ov)))))
        (crdt--enable-overlay-species 'org))
    (crdt--disable-overlay-species 'org)))

(defun crdt--org-overlay-advice (orig-fun &rest args)
  (if crdt-org-sync-overlay-mode
      (let ((crdt--track-overlay-species 'org))
        (apply orig-fun args))
    (apply orig-fun args)))

(cl-loop for command in '(org-cycle org-shifttab)
      do (advice-add command :around #'crdt--org-overlay-advice))

;;;; xscheme
(defvar crdt-xscheme-fcaps
  (crdt-make-local-fcaps
   '((xscheme-send-region (region))
     (xscheme-send-definition (point))
     (xscheme-send-previous-expression (point))
     (xscheme-send-next-expression (point))
     (xscheme-send-current-line (point))
     (xscheme-send-buffer)
     (xscheme-send-char)
     (xscheme-delete-output)
     (xscheme-send-breakpoint-interrupt)
     (xscheme-send-proceed)
     (xscheme-send-control-g-interrupt)
     (xscheme-send-control-u-interrupt)
     (xscheme-send-control-x-interrupt)
     (scheme-debugger-self-insert (last-command-event)))))
;; xscheme doesn't use standard DEFINE-*-MODE facility
;; and doesn't call after-change-major-mode-hook.
;; Therefore we have to hack.
(advice-add 'scheme-interaction-mode-initialize :after 'crdt--after-change-major-mode)
(advice-add 'scheme-debugger-mode-initialize :after
            (lambda () ;; haxxxx!!!!
              (let ((major-mode 'scheme-debugger-mode-initialize))
                (crdt--after-change-major-mode))))
;; I can't get input prompt from debugger to pop up at the right place.
;; Because it's done asynchronously in process filter,
;; and there seems to be no way to know the correct SPAWN-SITE-ID.

;;;; comint
(require 'ring)
(defvar comint-input-ring)
(defvar comint-input-ignoredups)
(defvar comint-input-ring-size)
(defvar comint-input-ring-file-name)

(defvar crdt-comint-fcaps
  (crdt-make-local-fcaps
   '((comint-send-input (point) (point))
     (comint-send-region (region) (region))
     (comint-send-eof (point)))))

(crdt-register-autoload 'shell-mode 'shell)
(crdt-register-autoload 'inferior-scheme-mode 'cmuscheme)
(crdt-register-autoload 'inferior-python-mode 'python)
(crdt-register-autoload 'prolog-inferior-mode 'prolog)
(crdt-register-autoload 'inferior-lisp-mode 'inf-lisp)

(put 'comint-input-ring 'crdt-variable-scheme crdt-variable-scheme-diff-server)

(defcustom crdt-comint-share-input-history 'censor
  "Share comint input history.
If the value is 'censor,
show only input history generated during a CRDT session to its peers,
Merge with history generated before the session after the buffer is no longer shared."
  :type '(choice boolean (const censor)))

(defvar-local crdt--comint-saved-input-ring nil)

(defun crdt--merge-ring (old-ring delta-ring nodups)
  "Construct a new ring by merging OLD-RING and DELTA-RING.
If NODUPS is non-nil, don't duplicate existing items in OLD-RING.
This procedure is non-destructive."
  (if delta-ring
      (let ((old-ring (copy-tree old-ring t)))
        (cl-loop for i from (1- (ring-length delta-ring)) downto 0
              for item = (ring-ref delta-ring i)
              do (if nodups
                     (let ((index (ring-member old-ring item)))
                       (when index
                         (ring-remove old-ring index))
                       (ring-insert old-ring item))
                   (ring-insert old-ring item)))
        old-ring)
    old-ring))

(defsubst crdt--comint-effective-ring ()
  (if crdt--comint-saved-input-ring
      (crdt--merge-ring crdt--comint-saved-input-ring comint-input-ring comint-input-ignoredups)
    comint-input-ring))

(defun crdt--comint-mode-hook ()
  (when (derived-mode-p 'comint-mode)
    (if crdt-mode
        (progn
          (add-to-list 'crdt--enabled-text-properties 'field)
          (add-to-list 'crdt--enabled-text-properties 'front-sticky)
          (add-to-list 'crdt--enabled-text-properties 'rear-nonsticky)
          (if (crdt--server-p)
              (when crdt-comint-share-input-history
                (crdt-register-variable 'comint-input-ring crdt-variable-scheme-diff-server)
                (when (eq crdt-comint-share-input-history 'censor)
                  (cl-shiftf crdt--comint-saved-input-ring comint-input-ring
                             (make-ring comint-input-ring-size))))
            (crdt-register-variable 'comint-input-ring crdt-variable-scheme-diff-server)
            (setq comint-input-ring-file-name nil)))
      (setq comint-input-ring (crdt--comint-effective-ring)
            crdt--comint-saved-input-ring nil))))

(defun crdt--comint-write-input-ring-advice (orig-func)
  (if crdt-mode
      (let ((comint-input-ring (crdt--comint-effective-ring)))
        (funcall orig-func))
    (funcall orig-func)))

(add-hook 'comint-mode-hook #'crdt--comint-mode-hook)
(add-hook 'crdt-mode-hook #'crdt--comint-mode-hook)

;;;; xref
(defvar crdt-xref-fcaps
  (crdt-make-local-fcaps
   `((xref-find-definitions (point) (point window)
                            ,(crdt-make-interactive-proxy 'xref-find-definitions))
     (xref-find-references (point) (point window)
                           ,(crdt-make-interactive-proxy 'xref-find-references))
     (xref-show-location-at-point (point) (point))
     (xref-pop-marker-stack () (point))
     (xref-goto-xref (point) (point window)))))

(defun crdt--xref-buffer-mode-hook ()
  (add-to-list 'crdt--enabled-text-properties 'xref-item)
  (add-to-list 'crdt--enabled-text-properties 'xref-group))

(provide 'crdt)
;;; crdt.el ends here
