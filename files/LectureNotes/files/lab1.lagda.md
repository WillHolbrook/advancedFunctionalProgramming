# Week 1 Lab Lecture

Agda has an interactive mode that is based on the text editor [emacs](resources.md). The objective of this lab is to begin to learn it.
There is also a [plugin for VS Code](resources.md), but we haven't tried it.

## These are instructions to be followed during the lab live lecture

## Learning objectives

 * Connect remotely to the lab.
 * Basic emacs.
 * Basic Agda interactive mode in emacs.
 * Run Agda in the lab.

## Important

The assessed tests for this module will be conducted exclusively in the School of Computer Science lab machines, and so it is important that you learn how to work in Agda with the lab machines, even if you plan to install Agda in your own machine for study purposes.

## Please login to a lab machine if you are physically in the lab

**Even if you have your own machine with you**.

See [remote lab access](remote-lab.md) for instructions about `ssh` installation.

## Connecting remotely to the lab

 * Now you will connect to the lab using `ssh`, even if you are already in the lab.

 * You will need to follow the same instructions to connect to the lab from your own machine when you are not physically present in the lab.

 1. Open a terminal.

 1. Connect to the gateway machine `tinky-winky` by typing

    `$ ssh username@tw.cs.bham.ac.uk`

    * Your username should be in *lowercase*.

    * You must use your School of Computer Science password if you set it to be different from your University password.

    * If you have forgotten it, go to [Account Help](https://my-account.cs.bham.ac.uk/).

 1. Once you are in `tinky-winky`, you need to go to the lab:

    `$ ssh-lab`

    * This will take you to a random lab machine.

    * The randomness is to balance the load.


 1. Now you should be logged in some lab machine. Type

    `$ module load agda`.

    * This will make agda available.

    * You need to do this *every time* you login to the lab, whether you do this remotely or locally.

    * You can do this automatically by adding it to the hidden file `.login`. We'll demonstrate how to do it with `emacs` during the lab lecture.

 1. After this, type

    `$ agda-mode setup`

    * You will need to this *only once*, but it doesn't harm if you do it repeatedly.

 1. After this, we will need to do some configuration so that `emacs` recognizes `.lagda.md` files and so that two Agda keyboard shortcuts are registered properly over `ssh`.
    You will need to do this only once. Type

    `$ emacs .emacs`

    * Add the lines
      ```terminal
      (add-to-list 'auto-mode-alist '("\\.lagda.md\\'" . agda2-mode))

      (add-hook 'agda2-mode-hook
	  (lambda () (progn
		       (local-set-key (kbd "C-c ,") 'agda2-goal-and-context)
		       (local-set-key (kbd "C-c .") 'agda2-goal-and-context-and-inferred))))
      ```
      anywhere.

    * Type `Ctrl-x Ctrl-s` to save the file.

    * Type `Ctrl-x Ctrl-c` to quit emacs.

 1. Now we will clone the AFP GitLab repository. You will need to do it only once in the lab machines.

    `$ git clone https://git.cs.bham.ac.uk/mhe/afp-learning.git`

    * We assume that you learned the basics of `git` in the module Functional Programming and possibly in other modules.

    * You will need to `git pull` regularly, as we update this repository regularly.

    * **Don't modify** any of the existing files as you will get conflicts.

    * If you want to experiment with any of the provided files, which you should certainly do when you are studying, make a copy of the file with a new name. Don't forget to change the line `module filename where` with the new name you have chosen.

 1. **Optional** suggestion to make your life easier when **working with your own machine**. We can't offer support for this, but feel free to ask on [Teams](https://teams.microsoft.com/l/team/19%3aR61tJG-pMjV401vTB2LyPJrPPpwhLzKQb2XbdwC9R5s1%40thread.tacv2/conversations?groupId=61980408-0833-4885-91fa-2ecde6c7c03f&tenantId=b024cacf-dede-4241-a15c-3c97d553e9f3).


    * If you work with your own machine, you will still need to use the lab machines from time to time, and in particular during the tests.

    * It is difficult to keep two different machines synchronized.

    * It is easy to lose files.

    * Your machine can break and it often does for some students, and so you should have backups.

    * For this you can use programs such as `scp`, `rsync` and `unison`. Look them up with a search engine.

    * But a **much easier** way is to use `sshfs`. Look for installation instructions with a search engine.

    * E.g. in `ubuntu`, you install it with `sudo apt install sshfs`.

    * Once you have it, create a directory named e.g. `lab`. Now type

      `sshfs remote-username@tw.cs.bham.ac.uk: /home/local-username/lab`

      Now magically, your files in the lab are available in the directory `lab` in your local machine. Before switching the machine off or closing your laptop lid, make sure you "umount" this, by ejecting it in the file manager. You can also do this with `$ sudo umount ~/lab`.

    * The above linux instructions are almost the same for `MacOS`. There are instructions on  the web.

    * In Windows this works differently, but there are instructions on the web.


    * The advantage of this approach is that (1) you don't need to synchronize, and (2) the School of Computer Science makes hourly, daily, weekly and monthly backups. Your files won't be lost, even if your machine breaks or the School servers break.

    * You can easily access the hourly, daily, weekly and monthly backups in the hidden directory `.snapshots`. Try this with

      `$ ls ~/.snapshot` in the lab, or
      `$ ls ~/lab/.snapshot` in your machine if you are using `sshfs`.

 1. Now let's edit our first Agda file from the terminal.

    ```terminal
    $ cd ~/afp-learning/files/LectureNotes/files/
    $ cp lab1.lagda.md my-lab1.lagda.md
    $ emacs my-lab1.lagda.md
    ```

    * Now you should be seeing this file in emacs. Find this position and start working following our verbal instructions.

    * In a browser, go to [Key bindings](https://agda.readthedocs.io/en/latest/tools/emacs-mode.html#keybindings).

    * In a browser, open [Emacs reference card](https://www.gnu.org/software/emacs/refcards/pdf/refcard.pdf).

## `Ctrl-g Ctrl-g`

You will need to type this when you start a sequence of emacs commands and then you want to give up without completing the sequence.

## Our first Agda file

Within emacs now type `Ctrl-c Ctrl-l`. This will "load" the Agda file and check it for correctness. The following program fragment has holes that we will fill interactively using the emacs mode for Agda. You can cheat by looking at the handout [introduction](introduction.lagda.md). But you *should not* copy and paste. Instead, you should learn and use the interactive mode following the lecturers verbal and visual instructions.

```agda
module my-lab1 where

Type = Set

data Bool : Type where
 true false : Bool

data Maybe (A : Type) : Type where
 nothing : Maybe A
 just    : A → Maybe A

data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

data ℕ : Type where
 zero : ℕ
 suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 10 _::_

data BinTree (A : Type) : Type where
 empty : BinTree A
 fork  : A → BinTree A → BinTree A → BinTree A

data RoseTree (A : Type) : Type where
 fork : A → List (RoseTree A) → RoseTree A

not : Bool → Bool
not x = {!!}

_&&_ : Bool → Bool → Bool
x && y = {!!}


_||_ : Bool → Bool → Bool
x || y = {!!}

infixr 20 _||_
infixr 30 _&&_

if_then_else_ : {A : Type} → Bool → A → A → A
if b then x else y = y

_+_ : ℕ → ℕ → ℕ
x + y = {!!}

_*_ : ℕ → ℕ → ℕ
x * y = {!!}

infixr 20 _+_
infixr 30 _*_

length : {A : Type} → List A → ℕ
length xs = {!!}

_++_ : {A : Type} → List A → List A → List A
xs ++ ys = {!!}

infixr 20 _++_

map : {A B : Type} → (A → B) → List A → List B
map f xs = {!!}

[_] : {A : Type} → A → List A
[ x ] = x :: []

reverse : {A : Type} → List A → List A
reverse xs = {!!}

rev-append : {A : Type} → List A → List A → List A
rev-append []        ys = ys
rev-append (x :: xs) ys = rev-append xs (x :: ys)

rev : {A : Type} → List A → List A
rev xs = rev-append xs []
```

## Now we will open emacs not from the command line, in the lab

Follow visual and verbal instructions by the lecturer.
