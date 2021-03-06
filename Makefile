VERSION = $(shell cat VERSION)

FILES = $(shell find src -name "*.clj")

all: conexp-clj-$(VERSION).zip
	@cp conexp-clj-$(VERSION).zip conexp-clj-$(VERSION)-$(shell date -u +"%Y%m%d%H%M%S").zip

target/conexp-clj-$(VERSION)-standalone.jar: $(FILES)
	@lein uberjar

conexp-clj-$(VERSION).zip: target/conexp-clj-$(VERSION)-standalone.jar
	@mkdir -p conexp-clj/lib/
	@cp stuff/libs/*.clj conexp-clj/lib
	@cp -r stuff/bin README.md conexp-clj/
	@cp -r src/res conexp-clj/lib/
	@cp target/conexp-clj-$(VERSION)-standalone.jar conexp-clj/lib/
	@zip -q -r conexp-clj-$(VERSION).zip conexp-clj

clean:
	@rm -rf conexp-clj/ lib/classes target/

distclean: clean
	@rm -rf lib conexp-clj-*.zip

test: clean
	@lein deps, test
