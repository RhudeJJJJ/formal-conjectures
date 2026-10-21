/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2333 : Family 10 := level10.get ⟨1038,by decide⟩
def sourceMap2333 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,0,1,2,3,4,5,6,7,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap2333 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap2333_checked : acceptsGraphIso
    (source (graph core2333) (root 10) 0 0) DegreeOneSmallSpectrum1625.graph sourceMap2333=true := by decide +kernel
theorem fusedMap2333_checked : acceptsGraphIso
    (fused (graph core2333) (root 10) 0 0) DegreeOneSmallSpectrum1629.graph fusedMap2333=true := by decide +kernel
theorem certified2333 : Certified (graph core2333) (root 10) 0 0 :=
  of_native_maps core2333 DegreeOneSmallSpectrum1625.graph DegreeOneSmallSpectrum1629.graph
    sourceMap2333 fusedMap2333 sourceMap2333_checked fusedMap2333_checked
    DegreeOneSmallComparisons.comparison2333
#print axioms sourceMap2333_checked
#print axioms fusedMap2333_checked
#print axioms certified2333
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
