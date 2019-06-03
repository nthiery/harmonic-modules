FROM sagemath/sagemath:8.7.beta3

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}
RUN sage -pip install -e .
RUN sage -jupyter nbextension install rise --py --sys-prefix
RUN sage -jupyter nbextension enable rise --py --sys-prefix
