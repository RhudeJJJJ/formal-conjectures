/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons48
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2444 : Family 10 := level10.get ⟨1409,by decide⟩
def sourceMap2444 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,0,1,2,3,4,5,6,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2444 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,12,2,3] (fusedLabel 10 0 0 v)
theorem sourceMap2444_checked : acceptsGraphIso
    (source (graph core2444) (root 10) 0 0) DegreeOneSmallSpectrum1982.graph sourceMap2444=true := by decide +kernel
theorem fusedMap2444_checked : acceptsGraphIso
    (fused (graph core2444) (root 10) 0 0) DegreeOneSmallSpectrum1975.graph fusedMap2444=true := by decide +kernel
theorem certified2444 : Certified (graph core2444) (root 10) 0 0 :=
  of_native_maps core2444 DegreeOneSmallSpectrum1982.graph DegreeOneSmallSpectrum1975.graph
    sourceMap2444 fusedMap2444 sourceMap2444_checked fusedMap2444_checked
    DegreeOneSmallComparisons.comparison2444
#print axioms sourceMap2444_checked
#print axioms fusedMap2444_checked
#print axioms certified2444
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
