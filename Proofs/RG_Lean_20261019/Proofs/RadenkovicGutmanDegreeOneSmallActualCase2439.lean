/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2439 : Family 10 := level10.get ⟨1362,by decide⟩
def sourceMap2439 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![1,0,9,10,11,12,4,5,6,7,8,2,3] (sourceLabel 10 0 0 v)
def fusedMap2439 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![5,0,1,2,3,4,8,9,10,11,12,6,7] (fusedLabel 10 0 0 v)
theorem sourceMap2439_checked : acceptsGraphIso
    (source (graph core2439) (root 10) 0 0) DegreeOneSmallSpectrum1736.graph sourceMap2439=true := by decide +kernel
theorem fusedMap2439_checked : acceptsGraphIso
    (fused (graph core2439) (root 10) 0 0) DegreeOneSmallSpectrum1970.graph fusedMap2439=true := by decide +kernel
theorem certified2439 : Certified (graph core2439) (root 10) 0 0 :=
  of_native_maps core2439 DegreeOneSmallSpectrum1736.graph DegreeOneSmallSpectrum1970.graph
    sourceMap2439 fusedMap2439 sourceMap2439_checked fusedMap2439_checked
    DegreeOneSmallComparisons.comparison2439
#print axioms sourceMap2439_checked
#print axioms fusedMap2439_checked
#print axioms certified2439
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
