CHAPTER_DIR := ../ComputationBook/Chapters

MD_DIR := src

NAMES :=  RegularLanguages \
		  SUMMARY

MD_FILES := $(foreach item,$(NAMES), $(MD_DIR)/$(item).md)

all: $(MD_FILES) 

$(MD_DIR)/%.md: $(CHAPTER_DIR)/%.lean 
	python3 dm.py $(CHAPTER_DIR)/$*.lean > $@

deploy:
	rm -rf ../docs
	cp -r book ../docs

clean:
	rm -f $(MD_DIR)/*.md \
	      