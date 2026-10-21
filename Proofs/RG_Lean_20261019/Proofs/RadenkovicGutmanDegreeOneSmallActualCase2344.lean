/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons46
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2344 : Family 10 := level10.get ⟨1065,by decide⟩
def sourceMap2344 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (sourceLabel 10 0 0 v)
def fusedMap2344 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,0,1,2,3,4,5,6,7,8,9,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2344_checked : acceptsGraphIso
    (source (graph core2344) (root 10) 0 0) DegreeOneSmallSpectrum1682.graph sourceMap2344=true := by decide +kernel
theorem fusedMap2344_checked : acceptsGraphIso
    (fused (graph core2344) (root 10) 0 0) DegreeOneSmallSpectrum1681.graph fusedMap2344=true := by decide +kernel
theorem certified2344 : Certified (graph core2344) (root 10) 0 0 :=
  of_native_maps core2344 DegreeOneSmallSpectrum1682.graph DegreeOneSmallSpectrum1681.graph
    sourceMap2344 fusedMap2344 sourceMap2344_checked fusedMap2344_checked
    DegreeOneSmallComparisons.comparison2344
#print axioms sourceMap2344_checked
#print axioms fusedMap2344_checked
#print axioms certified2344
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
