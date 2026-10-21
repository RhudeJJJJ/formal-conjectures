/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2148 : Family 10 := level10.get ⟨599,by decide⟩
def sourceMap2148 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,7,8,9,10,11,12,5,6,3,4] (sourceLabel 10 0 0 v)
def fusedMap2148 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,12,9,10] (fusedLabel 10 0 0 v)
theorem sourceMap2148_checked : acceptsGraphIso
    (source (graph core2148) (root 10) 0 0) DegreeOneSmallSpectrum1795.graph sourceMap2148=true := by decide +kernel
theorem fusedMap2148_checked : acceptsGraphIso
    (fused (graph core2148) (root 10) 0 0) DegreeOneSmallSpectrum1156.graph fusedMap2148=true := by decide +kernel
theorem certified2148 : Certified (graph core2148) (root 10) 0 0 :=
  of_native_maps core2148 DegreeOneSmallSpectrum1795.graph DegreeOneSmallSpectrum1156.graph
    sourceMap2148 fusedMap2148 sourceMap2148_checked fusedMap2148_checked
    DegreeOneSmallComparisons.comparison2148
#print axioms sourceMap2148_checked
#print axioms fusedMap2148_checked
#print axioms certified2148
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
