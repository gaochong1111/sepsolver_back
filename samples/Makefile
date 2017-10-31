#
# Makefile in samples
#
include ../Make.properties

F1_APP=f1app
F2_APP=f2app

SUBDIRS=$(F1_APP) $(F2_APP)

all: subdirs

subdirs:
	@for i in $(SUBDIRS); do \
		echo "===> $$i"; \
		(cd $$i && $(MAKE) -f $(MAKEFILE)) || exit 1; \
		echo "<=== $$i"; \
	done

clean:
	@for i in $(SUBDIRS); do \
		echo "===> $$i"; \
		(cd $$i && $(MAKE) clean -f $(MAKEFILE)) || exit 1; \
		echo "<=== $$i"; \
	done
