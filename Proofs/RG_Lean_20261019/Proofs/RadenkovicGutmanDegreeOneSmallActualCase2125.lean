/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2125 : Family 10 := level10.get ⟨564,by decide⟩
def sourceMap2125 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (sourceLabel 10 0 0 v)
def fusedMap2125 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2125_checked : acceptsGraphIso
    (source (graph core2125) (root 10) 0 0) DegreeOneSmallSpectrum1739.graph sourceMap2125=true := by decide +kernel
theorem fusedMap2125_checked : acceptsGraphIso
    (fused (graph core2125) (root 10) 0 0) DegreeOneSmallSpectrum1090.graph fusedMap2125=true := by decide +kernel
theorem certified2125 : Certified (graph core2125) (root 10) 0 0 :=
  of_native_maps core2125 DegreeOneSmallSpectrum1739.graph DegreeOneSmallSpectrum1090.graph
    sourceMap2125 fusedMap2125 sourceMap2125_checked fusedMap2125_checked
    DegreeOneSmallComparisons.comparison2125
#print axioms sourceMap2125_checked
#print axioms fusedMap2125_checked
#print axioms certified2125
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
