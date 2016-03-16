autoload -Uz colors ; colors
autoload -Uz compinit ; compinit
autoload -Uz add-zsh-hook

# Prompt

PROMPT='%U%F{red}Presburger%f%u>> '
RPROMPT=''

# ZLE

bindkey -e

# history

HISTFILE=$ZDOTDIR/.presburger_history
HISTSIZE=100000
SAVEHIST=100000
setopt extended_history
setopt hist_ignore_all_dups

# commands

tmux setw remain-on-exit on

base=$(cd $(dirname $0); pwd)
before=$(tmux split-window -h         -dPF '#{pane_id}' "echo before; rlwrap ./_before/main.native")
after=$( tmux split-window -t $before -dPF '#{pane_id}' "echo after; rlwrap ./_after/main.native")

send(){
    tmux send-keys -t $before "$@"
    tmux send-keys -t $after "$@"
}

states(){
    send STATES c-m; send "$1" c-m
}

sat(){
    send SAT c-m; send "$1" c-m
}

valid(){
    send VALID c-m; send "$1" c-m
}

pp(){
    send PP c-m; send "$1" c-m
}

interrupt(){
    send c-c
}

_exit_hook(){
    tmux kill-pane -t $before
    tmux kill-pane -t $after
    tmux setw remain-on-exit off
}

add-zsh-hook zshexit _exit_hook
