/* This file has been extracted from module RecursiveRecord. */
import java.util.NoSuchElementException;
import java.util.Optional;
public class RecursiveRecord {

  public final boolean a;
  public final Optional<RecursiveRecord> next;
  
  public RecursiveRecord getNext() throws NoSuchElementException {
    
    return this.next.get();
  }
  
  public RecursiveRecord() {
    
    this.a = false;
    this.next = Optional.ofNullable(null);
  }
  
  
}
