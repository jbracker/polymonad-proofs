
SOURCE_DIR = src

AGDA = agda

# Especially the Polymonad.Union proof runs out of stack space quickly.
AGDA_TC = $(AGDA) -i$(SOURCE_DIR) -v 0 +RTS -K40m -RTS


define agda-files-in
	$(shell find $(SOURCE_DIR)/$(1) -type f -name "*.agda" | grep -vxF -f "make-ignore")
endef

define agda-files-in-root
	$(shell find $(SOURCE_DIR)/*.agda | grep -vxF -f "make-ignore")
endef

define agda-in
	$(shell find $(SOURCE_DIR)/$(1) -type f -name "*.agda" | grep -vxF -f "make-ignore" | sed -e 's/\.agda\>/.agdai/g')
endef

all: type-check

type-check: only-base only-haskell only-hicks only-hicks only-polymonad only-supermonad only-theory
	
only-base: 
	$(foreach agda_file,$(call agda-files-in-root),$(AGDA_TC) $(agda_file) &&) true
	#

only-haskell:
	$(foreach agda_file,$(call agda-files-in,Haskell),$(AGDA_TC) $(agda_file) &&) true
	#

only-hicks: 
	$(foreach agda_file,$(call agda-files-in,Hicks),$(AGDA_TC) $(agda_file) &&) true
	#

only-polymonad: 
	$(foreach agda_file,$(call agda-files-in,Polymonad),$(AGDA_TC) $(agda_file) &&) true
	#

only-supermonad: 
	$(foreach agda_file,$(call agda-files-in,Supermonad),$(AGDA_TC) $(agda_file) &&) true
	#

only-theory: 
	$(foreach agda_file,$(call agda-files-in,Theory),$(AGDA_TC) $(agda_file) &&) true
	#

clean:
	find $(SOURCE_DIR) -type f -name "*.agdai" -delete 
	find $(SOURCE_DIR) -type f -name "*.agda~" -delete

%.agdai: %.agda
	$(AGDA_TC) $<