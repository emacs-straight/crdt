EMACS=emacs

.PHONY: package elpa clean compile

package: *.el
	@ver=`grep -o "Version: .*" crdt.el | cut -c 10-`; \
	tar czvf crdt-$$ver.tar.gz --mode 644 $$(find . -name \*.el)

elpa: *.el
	@version=`grep -o "Version: .*" crdt.el | cut -c 10-`; \
	dir=crdt-$$version; \
	mkdir -p "$$dir"; \
	cp $$(find . -name \*.el) crdt-$$version; \
	echo "(define-package \"crdt\" \"$$version\" \
	\"Simultaneous text editing over network\")" \
	> "$$dir"/crdt-pkg.el; \
	tar cvf crdt-$$version.tar --mode 644 "$$dir"

clean:
	@rm -rf crdt-*/ crdt-*.tar crdt-*.tar.gz *.elc

compile:
	${EMACS} -Q --batch -L . -f batch-byte-compile crdt.el
