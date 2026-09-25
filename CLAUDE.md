# Notes for Claude

## Pull requests: merge them yourself

I (ThisIsBad, the repository owner) authorize Claude to merge its own pull requests in this
repository without waiting for my review. Open PRs as regular (non-draft) PRs, then merge them
yourself with a merge commit once:

- the diff contains only the intended files;
- no credentials are included (`credentials.json` stays gitignored);
- every added Lean file compiles locally;
- the PR is mergeable and any CI on the head commit is green.

If a merge fails, fix the cause or report the blocker to me; never force it.
