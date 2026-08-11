REC := 16740866
ZST := .tar.zst
SUM := md5sum
EXT := $(ZST).$(SUM)
ALL := $(patsubst %$(EXT),%/,$(wildcard *$(EXT)))

all: $(ALL)

%$(ZST): %$(EXT)
	@curl --location "https://zenodo.org/records/$(REC)/files/$@" --remote-name --progress-bar
	@{ read SUM < "$<"; echo "$$SUM  $@"; } | $(SUM) --strict --check --warn -

%/: %$(ZST)
	@tar \
		--file "$^" \
		--zstd \
		--extract \
		--checkpoint \
		--checkpoint-action=dot \
		--strip-components=1 \
		--exclude='*.proof-*.smt2' \
		--directory='.' \
		--skip-old-files

	@chmod -R a-w $@

clean: $(foreach DIR,$(ALL),$(wildcard $(DIR)))
	@chmod --recursive u+w $^
	@rm --force --recursive $^
