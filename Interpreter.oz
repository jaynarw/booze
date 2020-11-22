declare Statement InitialStack Execute
Statement = [[nop] [nop] [nop]]
InitialStack = [semanticstack(Statement {Dictionary.new})]
% {Browse Environment}
proc {Execute SematicStack SingleAssignmentStore}
  case SematicStack
  of StackHead|RemainingStack then
    case StackHead 
    of semanticstack(Statement Environment) then
      {Browse [Statement Environment]}
      case Statement of
      StatHead|StatTail then
        if StatTail == nil then
          if StatHead == [nop] then
            {Browse nopdetected}
            {Execute RemainingStack SingleAssignmentStore}
          else
            {Execute RemainingStack SingleAssignmentStore}
          end
        else
          {Execute semanticstack(StatHead Environment)|semanticstack(StatTail Environment)|RemainingStack SingleAssignmentStore}
        end
      end
    end
  end
end
{Execute InitialStack {Dictionary.new}}
% Statement
% Environment (User Variable -> variable)
% SAS (Equivalence class) [<x>, <y>, <z>]

% case Statements
%   of []
%     then {Browse 'DONE'}
%   else
%     case SematicStack of 
%   {Browse Statements}
ST ([[no] [no] [no]])
ST [no] [[no] [no]]
ST [[no] [no]]
ST [no] [[no]]

