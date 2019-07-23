FLAGS = $(TOPFLAGS)

VERSION = -g 
#LIB_TYPE = {static,shared}
LIB_TYPE = $(LIB)
CXX = $(COMPILER)

ifeq ($(LIB_TYPE),shared)
   LIB_EXT = so
else
   LIB_EXT = a
endif

SRCS	=  \
	analysis_parse_1.cpp \
	petri_graphTransform_7.cpp \
	DFG_transform_4.cpp

OBJECTS = $(SRCS:.cpp=.o)


INCLUDE += /home/anushree1/verific_lib_eval/verilog
LINKDIRS += /home/anushree1/verific_lib_eval/verilog

INCLUDE += /home/anushree1/verific_lib_eval/vhdl
LINKDIRS += /home/anushree1/verific_lib_eval/vhdl

INCLUDE += /home/anushree1/verific_lib_eval/vhdl_sort
LINKDIRS += /home/anushree1/verific_lib_eval/vhdl_sort



INCLUDE += /home/anushree1/verific_lib_eval/verilog_nl
LINKDIRS += /home/anushree1/verific_lib_eval/verilog_nl





INCLUDE += /home/anushree1/verific_lib_eval/database
LINKDIRS += /home/anushree1/verific_lib_eval/database


INCLUDE += /home/anushree1/verific_lib_eval/util
LINKDIRS += /home/anushree1/verific_lib_eval/util

INCLUDE += /home/anushree1/verific_lib_eval/containers
LINKDIRS += /home/anushree1/verific_lib_eval/containers

HEADERS =  \
	analysis_parse.h \
	petri_graphTransform.h \
	DFG_transform.h

# 'libxnet' does not seem to be available on older SunOS5 systems.
# so use the finer set of many small .so files.
# 
# -pg version needs -ldl if -xnet is used only.
#
ifeq ($(shell uname),Darwin)
  OS = mac
  EXTLIBS = $(STATIC) -ltcl -ldl -lm -lc
endif
ifeq ($(shell uname),SunOS)
   EXTLIBS = -ldl -lsocket -lnsl -lm -lc
   OS = solaris
endif
ifeq ($(shell uname),Linux)
   EXTLIBS = -ldl -lnsl -lm -lc
   OS = linux
endif
LINKTARGET = analysis_parse-$(OS)


##########################################################################
# Stable for each Makefile

# BUILD NOTE: Unexpected behavior, including crashes, may occur if this
#             test example is not built with the same compile-time switches
#             that the verilog project library was built with.  Please
#             look at ../verilog/Makefile (../verilog/VeriCompileFlags.h) to 
#             see which switches were set.

CFLAGS = 
CFLAGS += $(FLAGS)

ifeq ($(CXX),)
    CXX = g++
endif

##########################################################################
# Now the make rules 

default: all

.SUFFIXES: .c .cpp .o 

.cpp.o:
	$(CXX) -c -I. $(patsubst %,-I../../../../%,$(INCLUDE)) $(VERSION) $(CFLAGS) $<

$(LINKTARGET) : $(OBJECTS) 
	$(CXX) $(VERSION) -o $(LINKTARGET) $(OBJECTS) $(patsubst %,../../../../%/*-$(OS).$(LIB_EXT),$(LINKDIRS)) $(EXTLIBS)  $(CFLAGS)

all : $(LINKTARGET) 

# Header file dependency : All my headers, and all included dir's headers
$(OBJECTS) : $(HEADERS) $(patsubst %,../../../../%/*.h,$(INCLUDE)) 
 
clean:
	rm -f $(LINKTARGET) $(OBJECTS)

