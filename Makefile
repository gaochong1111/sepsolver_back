#---------------------------------------
# FLAGS
#---------------------------------------
include Make.properties
#---------------------------------------
# FILES
#---------------------------------------
SRCDIR=src
SAMDIR=samples
SUBDIRS=$(SRCDIR) $(SAMDIR)
#---------------------------------------
# RULES
#---------------------------------------
all:
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
#---------------------------------------
# IMPLICIT RULES AND DEPENDENCIES
#---------------------------------------
