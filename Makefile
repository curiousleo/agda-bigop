AGDA=agda
AFLAGS=-i./Dependencies/agda-stdlib/src -i./src
SOURCE=Everything

check:
	cd src && ./generate_everything.sh
	$(AGDA) $(AFLAGS) src/$(SOURCE).agda
