.PHONY: build check-template clean shell

MAIN := main.tex

build: check-template
	docker compose run --build --rm latex

check-template:
	python3 scripts/check_template_format.py

clean:
	docker compose run --rm latex \
		latexmk -C -outdir=build $(MAIN)

shell:
	docker compose run --rm --entrypoint bash latex
