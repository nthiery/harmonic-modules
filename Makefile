talk.slides.html: talk.ipynb
	echo "jupyter nbconvert talk.ipynb --to slides" | sage -sh

install-talk: talk.slides.html
	rsync -av figures Nicolas.Thiery.name:www/talk/
	scp talk.slides.html Nicolas.Thiery.name:www/talk/index.html
