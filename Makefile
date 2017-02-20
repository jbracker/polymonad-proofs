
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

define agda-type-check
	$(AGDA_TC) $(1) && echo "Checked $(1)"
endef

define agda-check-all-in
	$(foreach agda_file,$(1),$(call agda-type-check,$(agda_file)) &&) true
endef

all: type-check

type-check: only-base only-haskell only-hicks only-hicks only-polymonad only-supermonad only-theory
	
only-base: 
	@$(call agda-check-all-in,$(call agda-files-in-root))

only-haskell:
	@$(call agda-check-all-in,$(call agda-files-in,Haskell))

only-hicks: 
	@$(call agda-check-all-in,$(call agda-files-in,Hicks))

only-polymonad: 
	@$(call agda-check-all-in,$(call agda-files-in,Polymonad))

only-supermonad: 
	@$(call agda-check-all-in,$(call agda-files-in,Supermonad))

only-theory: 
	@$(call agda-check-all-in,$(call agda-files-in,Theory))

clean:
	find $(SOURCE_DIR) -type f -name "*.agdai" -delete 
	find $(SOURCE_DIR) -type f -name "*.agda~" -delete
