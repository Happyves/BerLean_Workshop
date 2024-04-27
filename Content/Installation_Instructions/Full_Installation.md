

# Dependencies

Before installing Lean, you'll have to Install VS code and Git.

VS code is an IDE: a user interface (a programm) that allows you to nicely interact with Lean code. To install it, follow the instructions on:
https://code.visualstudio.com/ 

Git is a version management tool, which Lean uses to handle dependecies. It is apparently not possible to launch Lean if git isn't installed. To check whether it is installed on your laptop (it should be on Linux and macOS systems), open a terminal.
This is done by searching your laptop for a programm called one of "terminal", "shell", "cmd" or "command line" or "command prompt", and executing this programm. Then, type "git --version" and press Enter: if a version is displayed, you have git installed. Otherwise, please install git by following the instructions on:
https://git-scm.com/book/en/v2/Getting-Started-Installing-Git


# Installing Lean

Next, please follow the instructions from:
https://lean-lang.org/lean4/doc/quickstart.html
Once you have install the Lean VS code extention, in the documentation, you may skip the step "Books and Documentation" and follow that steps only up to "Install Lean Version Manager" included.


# Getting the material for this workshop

Open a folder in your folder explorer system where you would like the content of this workshop to be stored. Usually, by right-clicking the space there or by using the toolbar of the folder explorer, one of the options is to "open a terminal in this folder". Do this if you can. Otherwise, get the address of the folder you would like to store the workshop content in (which should be displayed by the folder explorer ; it has a pattern of form "username/Documents/MyCodeFolder"). Then, open the terminal as you did before write "cd" (for change directory) followed by the address (separated with a space), and press enter.

Then, exectute the following 3 lines in the terminal, one after the other:

git clone https://github.com/Happyves/BerLean_Workshop

cd BerLean_Workshop

lake exe cache get


# Final step

Finally, to launch VS code in the proper folder (that of the workshop), you can execute command "code ." (in the directory that you're in after having executed the previous commands).

To check that everything worked out, open the file explorer, if it isn't open already, by clicking the symbol with the two sheets just below the "File" tool-tab. Then go to "Content" and open "Test.lean". If nothing red is displayed on the screen once things have loaded, then you're good to go.