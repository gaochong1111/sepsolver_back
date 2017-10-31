#
# Makefile in src
#
include ../Make.properties
TARGET=sepsolver
# subdirs
SUBDIRS=$(foreach dir,$(shell find . -mindepth 1 -type d),$(shell echo $(dir) ' '))

# objs
# PARSER_OBJS=$(subst .cpp,.o,$(PARSER_DIR)/%.cpp)
# SOLVER_OBJS=$(subst .cpp,.o,$(SOLVER_DIR)/%.cpp)
# UTILS_OBJS=$(subst .cpp,.o,$(UTILS_DIR)/%.cpp)
# CPP_SRC_PATH = $(foreach dir,$(subst :, ,$(SUBDIRS)),$(wildcard $(dir)/*.cpp))

# ALL_OBJS=$(subst .cpp,.o,$(CPP_SRC_PATH))

all: subdirs $(TARGET)
	mv $(TARGET) $(DISTDIR)

subdirs:
	@for i in $(SUBDIRS); do \
		echo "===> $$i"; \
		(cd $$i && $(MAKE) -f $(MAKEFILE)) || exit 1; \
		echo "<=== $$i"; \
	done

$(TARGET):$(TEST_OBJS)
	ar -r $@ $^

.PHONY:clean
clean:
	@for i in $(SUBDIRS); do \
		echo "===> $$i"; \
		(cd $$i && $(MAKE) clean -f $(MAKEFILE)) || exit 1; \
		echo "<=== $$i"; \
	done
	rm -f $(DISTDIR)/$(TARGET)

