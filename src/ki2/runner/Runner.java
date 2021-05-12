package ki2.runner;

import java.io.IOException;

import jess.JessException;
import jess.Rete;
import jess.Value;
import jline.TerminalFactory;
import jline.TerminalSupport;
import jline.console.ConsoleReader;

public class Runner {

  public static void main(String[] args) {
    Rete r = new Rete();
    System.out.println("Welcome to Jess!\nPress Ctrl-Z to quit.");
    ConsoleReader reader = null;
    try {
      reader = new ConsoleReader(System.in, System.out, new TerminalSupport(true) {});
      reader.setPrompt("Jess> ");
      String line = null;
      line = reader.readLine();
      while (line != null) {
        String multiLine = null;
        multiLine = reader.readLine();
        while (!multiLine.isEmpty()) {
          line += multiLine;
          multiLine = reader.readLine();
        }
        try {
          Value result = r.eval(line);
          System.out.println(result.toString());
        } catch (JessException e) {
          System.out.println(e.getMessage());
        }
        line = reader.readLine();
      }
    } catch (IOException e) {
      e.printStackTrace();
    } finally {
      try {
        if (reader != null)
          reader.close();
        TerminalFactory.get().restore();        
      } catch (Exception e) {
        e.printStackTrace();
      }
    }
    System.out.println("Good Bye!");
  }

}
