FROM sagemath/sagemath:8.0-2

RUN sage -pip install tqdm rise

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
