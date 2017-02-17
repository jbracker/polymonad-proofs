
SOURCE_DIR = src

AGDA = agda

# Especially the Polymonad.Union proof runs out of stack space quickly.
AGDA_TC = $(AGDA) -i$(SOURCE_DIR) -v 0 +RTS -K40m -RTS


define agda-in
	$(shell find $(SOURCE_DIR)/$(1) -type f -name "*.agda" | grep -vxF -f "make-ignore" | sed -e 's/\.agda\>/.agdai/g')
endef

all: type-check

test:
	echo $(call agda-in,Theory)

type-check: only-base only-haskell only-hicks only-hicks only-polymonad only-supermonads only-theory
	
only-base: $(shell find $(SOURCE_DIR)/*.agda | sed -e 's/\.agda\>/.agdai/g')

only-haskell: $(call agda-in,Haskell)

only-hicks: $(call agda-in,Hicks)

only-polymonad: $(call agda-in,Polymonad)

only-supermonads: $(call agda-in,Supermonad)

only-theory: $(call agda-in,Theory)

clean:
	find $(SOURCE_DIR) -type f -name "*.agdai" -delete 
	find $(SOURCE_DIR) -type f -name "*.agda~" -delete

.PHONY: all type-check only-base only-haskell only-hicks only-polymonad only-supermonads only-theory test
%.agdai: %.agda
	$(AGDA_TC) $<