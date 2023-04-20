<img align="left" src="icon/icon-readme.png">

# @xamidi/pmGenerator

Code extracted from [deontic-logic/proof-tool](https://github.com/deontic-logic/proof-tool "GitHub repository") (still private; [readme](https://deontic-logic.github.io/readme.html)). Can be used to generate improved versions of [pmproofs.txt](https://us.metamath.org/mmsolitaire/pmproofs.txt "us.metamath.org/mmsolitaire/pmproofs.txt") of the [mmsolitaire](https://us.metamath.org/mmsolitaire/mms.html "us.metamath.org/mmsolitaire/mms.html") project.  
Exemplary generated results are available at [xamidi/mmsolitaire](https://github.com/xamidi/mmsolitaire "GitHub repository").  
Eligible for high-performance computing. If you have access to a powerful computer, please consider to use this tool to further contribute to our knowledge regarding minimal proofs.  
The following table exemplary shows progress that has already been made.

|                                                                                         Load Files up to..                                                                                                      | Size of Files (with conclusions) [B] | Required Memory (approx.) [GiB] |                                                                 Recent Growth Factor                                                                 |
| --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | ------------------------------------:| -------------------------------:| ----------------------------------------------------------------------------------------------------------------------------------------------------:|
| [dProofs29.txt](https://github.com/xamidi/pmGenerator/tree/master/data/dProofs-withConclusions "735'676'962 bytes compressed into 41'959'698 bytes (ratio approx. 17.5329)")                                    |                          735 676 962 |                            2.68 | [3.3613...](https://www.wolframalpha.com/input?i=516720692%2F153725015 "size(dProofs29.txt) / size(dProofs27.txt)")                                  |
| [dProofs31&#x2011;unfiltered31+.txt](https://mega.nz/file/G18AWIpC#B04xOdtQj_2PJJP0yNQxbim7pOgd-hwv1i1EVU6ZsTM "2'161'632'450 bytes compressed into 112'364'583 bytes (ratio approx. 19.2377)")                 |                        2 897 309 412 |                            9.84 | [4.1833...](https://www.wolframalpha.com/input?i=2161632450%2F516720692 "size(dProofs31-unfiltered31+.txt) / size(dProofs29.txt)")                   |
| [dProofs33&#x2011;unfiltered31+.txt](https://mega.nz/file/3gVQSIJL#Qfa9CoUwsHWYYNHXYaP1mg61QQSJ1NSl1CHudK4g7BA "8'349'023'875 bytes compressed into 402'886'507 bytes (ratio approx. 20.7230)")                 |                       11 246 333 287 |                           36.49 | [3.8623...](https://www.wolframalpha.com/input?i=8349023875%2F2161632450 "size(dProofs33-unfiltered31+.txt) / size(dProofs31-unfiltered31+.txt)")    |
| [dProofs35&#x2011;unfiltered31+.txt](https://mega.nz/file/2893yZ7S#JlCHv4uOajgBJPPE2W87F_LAPzkH0-FlF4_2OrccuC4 "30'717'801'573 bytes compressed into 1'400'853'331 bytes (ratio approx. 21.9279)")              |                       41 964 134 860 |                          130.52 | [3.6792...](https://www.wolframalpha.com/input?i=30717801573%2F8349023875 "size(dProofs35-unfiltered31+.txt) / size(dProofs33-unfiltered31+.txt)")   |
| [dProofs37&#x2011;unfiltered31+.txt](https://mega.nz/file/6wUyDQzT#DQIJOLd5dCn-6V9sJWiJXeGRPUTUaA-7LqbGfLStjV0 "113'174'356'461 bytes compressed into 4'897'020'927 bytes (ratio approx. 23.1109)")<sup>✻</sup> |                      155 138 491 321 |                          485.12 | [3.6843...](https://www.wolframalpha.com/input?i=113174356461%2F30717801573 "size(dProofs37-unfiltered31+.txt) / size(dProofs35-unfiltered31+.txt)") |

This tool has been [posted](https://groups.google.com/g/metamath/c/6DzIY33mthE/m/K0I6UNoiAgAJ) to the Metamath mailing list.

#### Usage
    pmGenerator ( -g <limit> [-u] [-c] | -r <pmproofs file> <output file> [-i <prefix>] [-c] [-d] | -a <initials> <replacements file> <pmproofs file> <output file> [-s] [-l] [-w] [-d] | -f ( 0 | 1 ) [-i <prefix>] [-o <prefix>] [-d] | -p [-i <prefix>] [-s] [-t] [-x <limit>] [-y <limit>] [-o <output file>] [-d] )+ | -m <limit>
    -g: Generate proof files
        -u: unfiltered (significantly faster, but generates redundant proofs)
        -c: proof files without conclusions, requires additional parsing
    -r: Replacements file creation based on proof files
        -i: customize input file path prefix ; default: "data/dProofs-withConclusions/dProofs"
        -c: proof files without conclusions, requires additional parsing ; sets default input file path prefix to "data/dProofs-withoutConclusions/dProofs"
        -d: print debug information
    -a: Apply replacements file
        -s: style all proofs (replace proofs with alphanumerically smaller variants)
        -l: list all proofs (i.e. not only modified proofs)
        -w: wrap results
        -d: print debug information
    -f: Create proof files with removed (-f 0) or added (-f 1) conclusions from proof files of the other variant
        -i: customize input file path prefix ; default: "data/dProofs-withConclusions/dProofs" or "data/dProofs-withoutConclusions/dProofs"
        -o: customize output file path prefix ; default: "data/dProofs-withoutConclusions/dProofs" or "data/dProofs-withConclusions/dProofs"
        -d: print debug information
    -p: Print conclusion length plot data
        -i: customize input file path prefix ; requires files with conclusions ; default: "data/dProofs-withConclusions/dProofs"
        -s: measure symbolic length (in contrast to conclusion representation length)
        -t: table arrangement, one data point per row
        -x: upper horizontal limit
        -y: upper vertical limit
        -o: print to given output file
        -d: print debug information
    -m: MPI-based multi-node filtering (-m <n>) of a first unfiltered proof file (with conclusions) at ./data/dProofs-withConclusions/dProofs<n>-unfiltered<n>+.txt. Creates dProofs<n>.txt.
        Cannot be combined with further commands.

#### Examples
    pmGenerator -g -1
    pmGenerator -r "data/pmproofs.txt" "data/pmproofs-reducer.txt" -i "data/dProofs" -c -d
    pmGenerator -a SD data/pmproofs-reducer.txt data/pmproofs.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d
    pmGenerator -g 19 -g 21 -u -r data/pmproofs-old.txt data/pmproofs-reducer.txt -d -a SD data/pmproofs-reducer.txt data/pmproofs-old.txt data/pmproofs-result-styleAll-modifiedOnly.txt -s -w -d
    pmGenerator -f 0 -o data/dProofs-withoutConclusions_ALL/dProofs -d
    pmGenerator -p -s -d -p -s -t -x 50 -y 100 -o data/plot_data_x50_y100.txt
    pmGenerator -m 17

#### Navigation
- [C++11 branch](https://github.com/xamidi/pmGenerator/tree/c++11)
- [C++20 branch](https://github.com/xamidi/pmGenerator/tree/master)

<sup>✻</sup><sub>Generation and utilization were performed with computing resources granted by RWTH Aachen University under project [rwth1392](pdf/rwth1392_abstract.pdf "View rwth1392_abstract.pdf").</sub>
