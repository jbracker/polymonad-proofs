

REMOVE = rm -f

AGDA = agda

AGDA_TC = $(AGDA) -v 0

all: type-check



type-check:
	$(AGDA_TC) Utilities.agda
	$(AGDA_TC) Haskell.agda
	$(AGDA_TC) Identity.agda
	$(AGDA_TC) Monad.agda
	$(AGDA_TC) Polymonad.agda
	$(AGDA_TC) Hicks/Polymonad.agda
	$(AGDA_TC) Hicks/Equivalency.agda
	$(AGDA_TC) Hicks/UniqueBinds.agda
	$(AGDA_TC) Polymonad/Composable.agda
	$(AGDA_TC) Polymonad/Principal.agda
	$(AGDA_TC) Polymonad/Composition.agda

clean:
	$(REMOVE) *.agdai
	$(REMOVE) Monad/*.agdai
	$(REMOVE) Parameterized/*.agdai
	$(REMOVE) Parameterized/IndexedMonad/*.agdai
	$(REMOVE) Polymonad/*.agdai
	$(REMOVE) Polymonad/MorphMonad/*.agdai