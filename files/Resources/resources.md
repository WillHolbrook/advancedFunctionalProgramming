# Resources

## Agda installation

We offer you a complete Agda environment in the UG04 Lab machines, either in person of [remotely](remote-lab.md).

so that you don't need to install it in your own machine. We also explain how to work remotely in the first [lab lecture](/files/LectureNotes/files/lab1.lagda.md).

We are using Agda 2.6.2, the latest version at the time of writing. There is a standard library, but we are not going to use it.

You may still wish to [install Agda in your own machine](https://agda.readthedocs.io/en/latest/getting-started/installation.html), but we are not able to provide support, although you are welcome to ask questions on Teams.
It is much easier to install on Linux and Mac, and possible on Windows (one option is to use the Window Subsystem Linux (WSL) and use the Linux installation guide).

## Agda resources that you will need for daily use

 * [Getting started](https://agda.readthedocs.io/en/latest/getting-started/index.html) with Agda.
 * [Language reference](https://agda.readthedocs.io/en/latest/language/index.html)
 * [Agda mode](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html)
 * [Agda mode key bindings](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#keybindings)
 * [Global commands](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#global-commands)
 * [Commands in context of a goal](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#commands-in-context-of-a-goal)
 * [Other commands](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#other-commands)
 * [Unicode input](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#unicode-input)

## Emacs resources

Agda has a very nice interactive environment for writing programs which works in the text editor [emacs](http://www.gnu.org/software/emacs/).

 * [Install emacs](https://www.gnu.org/software/emacs/download.html)
 * [A guided tour of Emacs](https://www.gnu.org/software/emacs/tour/index.html)
 * [Emacs manual](https://www.gnu.org/software/emacs/manual/html_node/emacs/index.html)
 * [Emacs reference card](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf)
 * [A tutorial introduction to emacs](https://www2.lib.uchicago.edu/keith/tcl-course/emacs-tutorial.html)

The [Getting Started](https://plfa.github.io/GettingStarted/) section of the online book
[Programming Language Foundations in Agda](https://plfa.github.io/) has a nice installation guide as well as a summary of emacs commands.

We will maintain a sample emacs configuration file which you may wish to use as a reference [here](https://git.cs.bham.ac.uk/mhe/afp-learning/-/blob/main/files/Resources/sample.emacs).

## Missing unicode symbols on Windows via `ssh`

If you are on Windows and are using `ssh` to access lab machines through Powershell (or some other emulator) and some unicode symbols are not displayed, then you could try installing and using [Windows Terminal](https://www.microsoft.com/en-us/p/windows-terminal/9n0dx20hk701?activetab=pivot:overviewtab) as an alternative to Powershell. Windows Terminal has full unicode support and can be found in the Microsoft Store.

## Installing Agda on Windows

For Windows users who want to install Agda locally, you can do the following:

1. Open `PowerShell` with Admin privs

1. Install Chocolatey:

   `Set-ExecutionPolicy Bypass -Scope Process -Force; [System.Net.ServicePointManager]::SecurityProtocol = [System.Net.ServicePointManager]::SecurityProtocol -bor 3072; iex ((New-Object System.Net.WebClient).DownloadString('https://community.chocolatey.org/install.ps1'))`

1. Install cabal:

   `choco install cabal`

1. Update cabal:

   `cabal update`

1. Install ghci:

   `cabal install --lib ghci`

1. Install Agda:

   `cabal install Agda`

1. Install emacs:

   `choco install emacs`

1. Setup Agda:

   `agda-mode setup`

1. Install DejaVu Sans Mono and Symbola fonts -- make the former your default font and the latter your fallback font by adding the following to your .emacs file:

   `(set-fontset-font "fontset-default" nil (font-spec :name "DejaVu Sans Mono"))`
   `(set-fontset-font t nil "Symbola" nil 'append)`

For questions about Windows installation, ask our lecturer Todd Ambridge in the lab or on Teams.

## Visual Studio Code

There is [plugin for Agda support](https://marketplace.visualstudio.com/items?itemName=banacorn.agda-mode) available on the Visual Studio Marketplace. We haven't tried it.

## Further reading

 * [The Agda Wiki](https://wiki.portal.chalmers.se/agda/pmwiki.php)
 * [Agda tutorials](https://wiki.portal.chalmers.se/agda/Main/Othertutorials)
 * [Dependently Typed Programming in Agda](http://www.cse.chalmers.se/~ulfn/papers/afp08/tutorial.pdf)
 * [Dependent types at work](http://www.cse.chalmers.se/~peterd/papers/DependentTypesAtWork.pdf)

## Advanced reading

 * [Programming Language Foundations in Agda](https://plfa.github.io/)
