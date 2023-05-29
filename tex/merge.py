from io import StringIO
import re

starting_point = 'main.tex'

def unfold(file):
    
  # read file
  with open(file, 'r') as f:
    content = f.read()

  # if there is an \include{...} command,
  # replace it with the content of the file
  # if there is not such command, do nothing

  # find the first \include{...} command
  # if there is no such command, return the content
  # of the file
  m = re.search(r'\\include{(.*)}', content)
  if m is None:
    return content
  else:
    # get the file name
    file_name = m.group(1) + '.tex'
    # get the content of the file
    file_content = unfold(file_name)
    # replace the \include{...} command with the content
    content = re.sub(r'\\include{.*}', file_content, content, count=1)
    # return the content
    return content
  
print(unfold(starting_point))