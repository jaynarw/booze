% Statement
% Environment (User Variable -> variable)
% SAS (Equivalence class) [<x>, <y>, <z>]

declare Statement InitialStack Execute Concat
fun {Concat Xs Ys}
  {FoldR Xs fun {$ A B} A|B end Ys}
end
Statement = [[nop] [nop] [nop]]
InitialStack = [semanticstack(Statement {Dictionary.new})]
proc {Execute SematicStack SingleAssignmentStore}
  case SematicStack
  of StackHead|RemainingStack then
    case StackHead 
    of semanticstack(Statement Environment) then
      if Statement == [nop] then
        {Browse [s k i p]}
        {Execute RemainingStack SingleAssignmentStore}
      else
        {Execute {Concat {Map Statement fun {$ A} semanticstack(A Environment) end} RemainingStack} SingleAssignmentStore}
      end
    end
  end
end
{Execute InitialStack {Dictionary.new}}
