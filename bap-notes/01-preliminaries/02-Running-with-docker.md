# Running BAP with Docker

Instructions for installing BAP manually can be found on the official BAP website: https://github.com/BinaryAnalysisPlatform/bap. 

BAP releases a docker image containing the latest version of the master branch:

```
docker pull binaryanalysisplatform/bap:latest
```

Run the container:

```
docker run --rm -ti binaryanalysisplatform/bap:latest bash
```

Then confirm that the relevant executables are present:

```
bap --version
bapbuild -help
bapbundle -help
```

To exit:

```
exit
```

To mount your `${HOME}` directory in the container:

```
docker run --rm -ti -v ${HOME}:/external -w /external binaryanalysisplatform/bap:latest bash
```

Then your home directory will be available at `/external` inside the container:

```
pwd
ls
```

For example, if you have a file at `${HOME}/foo.txt` on your local computer, you can see it and edit it from inside your container:

```
cat /external/foo.txt
```