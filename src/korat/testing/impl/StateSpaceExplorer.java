package korat.testing.impl;

import java.util.IdentityHashMap;
import java.util.Map;
import java.util.Arrays;

import korat.finitization.IFinitization;
import korat.finitization.impl.ArraySet;
import korat.finitization.impl.CVElem;
import korat.finitization.impl.CandidateBuilder;
import korat.finitization.impl.ClassDomain;
import korat.finitization.impl.FieldDomain;
import korat.finitization.impl.Finitization;
import korat.finitization.impl.ObjSet;
import korat.finitization.impl.StateSpace;
import korat.instrumentation.IKoratArray;
import korat.testing.IKoratSearchStrategy;
import korat.utils.IIntList;
import korat.utils.IntListAI;
import korat.config.ConfigManager;

/**
 * StateSpaceExplorer implements Korat search strategy
 * 
 * @author Sasa Misailovic <sasa.misailovic@gmail.com>
 * 
 */
public class StateSpaceExplorer implements IKoratSearchStrategy {

    protected StateSpace stateSpace;

    protected CandidateBuilder candidateBuilder;

    protected int[] candidateVector;
    
    protected int[] startCV;
    
    protected int[] endCV;

    protected IIntList accessedFields;

    protected IIntList changedFields;

    protected boolean isSecondCV = false;

    protected boolean isFirstGenCV = false;

    //protected boolean alyasFrstPrdOk = false;
    
    protected int prevlastAccessedFieldIndex = 0;


    protected ConfigManager config = ConfigManager.getInstance();//alyas

    //protected boolean toJump = config.jump;
    protected long toJump = config.jump;

    public StateSpaceExplorer(IFinitization ifin) {
        Finitization fin = (Finitization)ifin; 
        stateSpace = fin.getStateSpace();

        int totalNumberOfFields = stateSpace.getTotalNumberOfFields();
        accessedFields = new IntListAI(totalNumberOfFields);

        changedFields = new IntListAI(totalNumberOfFields);
        for (int i = 0; i < totalNumberOfFields; i++)
            changedFields.add(i);

        candidateBuilder = new CandidateBuilder(stateSpace, changedFields);
        candidateVector = new int[totalNumberOfFields];

        startCV = fin.getInitialCandidateVector();

        endCV = null;
        
    }

    /*
     * -------------------------------------------------------------------------
     * Implementation of IKoratSearchStrategy interface.
     * -------------------------------------------------------------------------
     */
    public IIntList getAccessedFields() {
        return accessedFields;
    }

    public int[] getCandidateVector() {
        return candidateVector;
    }

    public void setEndCandidateVector(int[] endCV) {
        if (endCV.length != candidateVector.length)
            throw new RuntimeException("Invalid length of end candidate vector");
        this.endCV = endCV;
    }

    public void setStartCandidateVector(int[] startCV) {
        if (startCV.length != candidateVector.length)
            throw new RuntimeException("Invalid length of start candidate vector");
        this.startCV = startCV;
    }
    
    protected boolean firstTestCase = true;

    public Object nextTestCase() {
        if (firstTestCase) {
            firstTestCase = false;
            // candidate vector to start vector
            candidateVector = startCV;
        } else {
            // find next candidate vector
            boolean hasNext = getNextCandidate();
            if (!hasNext) {
                // if vector is invalid, return null
                return null;
            }
        }
        return candidateBuilder.buildCandidate(candidateVector);
    }
    
    /*
     * -------------------------------------------------------------------------
     * Internal stuff.
     * -------------------------------------------------------------------------
     */                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                         
    
    protected boolean getNextCandidate() {
        boolean nextCandidateFound = false;
        
        changedFields.clear();
      
        while (!nextCandidateFound) { //while true then continue in loop
            if (accessedFields.isEmpty())
                break; // candidate not found - search is completed

            int lastAccessedFieldIndex = accessedFields.removeLast();
            CVElem lastAccessedField = stateSpace.getCVElem(lastAccessedFieldIndex);
            FieldDomain fDomain = stateSpace.getFieldDomain(lastAccessedFieldIndex);
            int maxInstanceIndexForFieldDomain = fDomain.getNumberOfElements() - 1;
            int currentInstanceIndex = candidateVector[lastAccessedFieldIndex];
            
            if (lastAccessedField.isExcludedFromSearch()){ //array fields are exempt from search
                nextCandidateFound = false;      
            } else if (currentInstanceIndex >= maxInstanceIndexForFieldDomain) { 
                //Max here depend on the domain, so may change from 0 to 2
                candidateVector[lastAccessedFieldIndex] = 0;
                changedFields.add(lastAccessedFieldIndex);
                nextCandidateFound = false;
            } else {
                /*
                 * if we wanted just to exercise pruning, without
                 * non-isomorphism checks the following lines would suffice:
                 * candidateVector[lastAccessedField]++; 
                 * nextCandidateFound = true;
                 */

                int numberOfAccessedFields = accessedFields.numberOfElements();
                int maxInstanceIndexInClassDomain = -1;

                ClassDomain cDomain = fDomain.getClassDomainFor(currentInstanceIndex);
                
                if (fDomain.isPrimitiveType()
                        || !cDomain.isIncludedInIsomorphismChecking()) {
                    //if(!fDomain.isPrimitiveType()) System.out.println("primitive");
                //1
                    if(toJump > 0 && toJump < 5){
                //if(toJump){
                 // switch (toJump) {
                 //   case 0:
                        /**We have 4 status within the jump option 1=All(ABC), 2=A, 3=AB, 4=AC
                        Both case A & B for primitive except C for Obj.s
                        */

                        //CASE A
                           if (isSecondCV && lastAccessedFieldIndex > maxInstanceIndexForFieldDomain && lastAccessedFieldIndex < prevlastAccessedFieldIndex
                                && !fDomain.isPrimitiveType()
                                && isFirstGenCV
                                //&& TestCradle.predicateOK
                                ){  
                                //isSecondCV req, (lastAccessedFieldIndex > maxInstanceIndexForFieldDomain) req !fDomain.isPrimitiveType() reg at redtree
                                //, && lastAccessedFieldIndex < prevlastAccessedFieldIndex opt
                                //System.out.println("Ok0 ");
                                int max = 0;
                                for (int ktr = 0; ktr < lastAccessedFieldIndex; ktr++) {
                                    if (candidateVector[ktr] > max && candidateVector[ktr] != maxInstanceIndexForFieldDomain)
                                    max = candidateVector[ktr];
                                }
                                if(candidateVector[lastAccessedFieldIndex] == max) { 
                                //candidateVector[lastAccessedFieldIndex] = max;
                                    candidateVector[lastAccessedFieldIndex] = maxInstanceIndexForFieldDomain;
                                    //System.out.println("Okmax");
                                }
                                else candidateVector[lastAccessedFieldIndex] = max;
                            }
                            else candidateVector[lastAccessedFieldIndex]++;
                        //CASE B
                        if(toJump == 1 || toJump == 3){
                            //if (isSecondCV) {
                                //if (maxInstanceIndexForFieldDomain % 2 == 0) candidateVector[lastAccessedFieldIndex]++; //even jump
                                //else candidateVector[lastAccessedFieldIndex] = candidateVector[lastAccessedFieldIndex] + 2;
                                //System.out.println("Ok ");
                                if (TestCradle.predicateOK && !fDomain.isPrimitiveType()
                                    //&& isFirstGenCV
                                    ) {
                                    //System.out.println("Ok1 ");
                                    int max = 0;
                                    for (int ktr = 0; ktr < lastAccessedFieldIndex; ktr++) {
                                        if (candidateVector[ktr] > max && candidateVector[ktr] != maxInstanceIndexForFieldDomain)
                                        max = candidateVector[ktr]; 
                                    }
                                    candidateVector[lastAccessedFieldIndex] = maxInstanceIndexForFieldDomain;
                                    //alyasFrstPrdOk = true;
                                }
                            //}
                        }//end if for case B where 
                            isSecondCV = true;
                            if (candidateVector[lastAccessedFieldIndex] > maxInstanceIndexForFieldDomain) {
                                candidateVector[lastAccessedFieldIndex] = 0;
                                changedFields.add(lastAccessedFieldIndex);
                                nextCandidateFound = false;
                            }else {
                                changedFields.add(lastAccessedFieldIndex);
                                nextCandidateFound = true;
                            }
                    //        break;    
                    }//end if toJump
                    else{
                        candidateVector[lastAccessedFieldIndex]++;
                        changedFields.add(lastAccessedFieldIndex);
                        nextCandidateFound = true;
                    }
                //2 end check for premitive & !Iso
                } else { //We looking for Objs fields CV
                    //System.out.println("Ok2 ");
                    for (int i = 0; i < numberOfAccessedFields; i++) {
                        int accessedFieldIndex = accessedFields.get(i);
                        int activeInstanceIndex = candidateVector[accessedFieldIndex];
                        
                        FieldDomain fd = stateSpace.getFieldDomain(accessedFieldIndex);
                        ClassDomain cd = fd.getClassDomainFor(activeInstanceIndex);

                        if (cd != null && cd == (cDomain)) {
                            int instanceIndex = fd.getClassDomainIndexFor(activeInstanceIndex);
                            if (maxInstanceIndexInClassDomain < instanceIndex)
                                maxInstanceIndexInClassDomain = instanceIndex;
                        }
                    }

                    int currentInstanceIndexInClassDomain = fDomain.getClassDomainIndexFor(currentInstanceIndex);
                    //3
                    if (currentInstanceIndexInClassDomain <= maxInstanceIndexInClassDomain) {
                        //CASE C
                        if (toJump == 1 || toJump == 4 || toJump == 5){
                            int max = 0;
                            for (int ktr = 0; ktr < lastAccessedFieldIndex; ktr++) {
                                if (candidateVector[ktr] > max) max = candidateVector[ktr];
                            }
                            candidateVector[lastAccessedFieldIndex]++;
                            if (TestCradle.predicateOK && lastAccessedFieldIndex < prevlastAccessedFieldIndex
                                //&& isFirstGenCV
                                ) {
                                candidateVector[lastAccessedFieldIndex] = max;
                            }
                            if (candidateVector[lastAccessedFieldIndex] > maxInstanceIndexForFieldDomain) { 
                                candidateVector[lastAccessedFieldIndex] = 0;
                                changedFields.add(lastAccessedFieldIndex);
                                nextCandidateFound = false;
                            }else {
                                changedFields.add(lastAccessedFieldIndex);
                                nextCandidateFound = true;
                            }//ALYAS
                        }else {
                        candidateVector[lastAccessedFieldIndex]++;
                        changedFields.add(lastAccessedFieldIndex);
                        nextCandidateFound = true;
                        }
                    //4
                    }else {
                        int nextInstanceIndex = fDomain.getIndexOfFirstObjectInNextClassDomain(currentInstanceIndex);
                        if (nextInstanceIndex == -1) { //We reached to the end
                            candidateVector[lastAccessedFieldIndex] = 0;
                            changedFields.add(lastAccessedFieldIndex);
                            nextCandidateFound = false;
                        } else {
                            candidateVector[lastAccessedFieldIndex] = nextInstanceIndex;
                            changedFields.add(lastAccessedFieldIndex);
                            nextCandidateFound = true;

                        }

                    }
                }//end else looking for obj
            }//end else check for new CV
            if (toJump > 0 && toJump < 6) prevlastAccessedFieldIndex = lastAccessedFieldIndex;
            if (TestCradle.predicateOK) isFirstGenCV = true;
            //if (toJump) prevlastAccessedFieldIndex = lastAccessedFieldIndex;
        }// end while

        if (nextCandidateFound) {
            nextCandidateFound = !reachedEndCV();
        }
        return nextCandidateFound;

    }

    private boolean reachedEndCV() {
        
        if (endCV == null)
            return false;
        for (int i = 0; i < candidateVector.length; i++) {
            if (candidateVector[i] != endCV[i])
                return false;
        }
        return true;
        
    }
    
    Map<Object, Object> visited = new IdentityHashMap<Object, Object>();

    public void reportCurrentAsValid() {
        visited.clear();
        Object root = stateSpace.getRootObject();
        touch(root);       
    }
       
    protected void touch(Object obj) {
    
        visited.put(obj, null);
        int[] objFlds = stateSpace.getFieldIndicesFor(obj);
        for (int fldIndex : objFlds) 
            touchField(fldIndex);

    }

    private void touchField(int fldIndex) {
    
        accessedFields.add(fldIndex);

        FieldDomain fd = stateSpace.getFieldDomain(fldIndex);
        if (fd.isPrimitiveType())
            return;

        int fldValueIndex = candidateVector[fldIndex];

        Object value = null;
        if (fd.isArrayType()) {
        
            value = ((ArraySet) fd).getArray(fldValueIndex);
            if (!visited.containsKey(value))
                touchArray(value);
            
        } else {
        
            value = ((ObjSet) fd).getObject(fldValueIndex);
            if (value!=null && !visited.containsKey(value))
                touch(value);
            
        }   
             
    }

    private void touchArray(Object obj) {
        visited.put(obj, null);
        
        int[] objFlds = stateSpace.getFieldIndicesFor(obj);
        IKoratArray arr = (IKoratArray) obj;
        
        int length = arr.getLength();
        for (int i = 0; i < length + 1; i++) {
            touchField(objFlds[i]);
        }
       
    }

}
