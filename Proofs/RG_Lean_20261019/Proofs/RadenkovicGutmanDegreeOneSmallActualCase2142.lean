/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons42
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2142 : Family 10 := level10.get ⟨591,by decide⟩
def sourceMap2142 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (sourceLabel 10 0 0 v)
def fusedMap2142 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2142_checked : acceptsGraphIso
    (source (graph core2142) (root 10) 0 0) DegreeOneSmallSpectrum1814.graph sourceMap2142=true := by decide +kernel
theorem fusedMap2142_checked : acceptsGraphIso
    (fused (graph core2142) (root 10) 0 0) DegreeOneSmallSpectrum1137.graph fusedMap2142=true := by decide +kernel
theorem certified2142 : Certified (graph core2142) (root 10) 0 0 :=
  of_native_maps core2142 DegreeOneSmallSpectrum1814.graph DegreeOneSmallSpectrum1137.graph
    sourceMap2142 fusedMap2142 sourceMap2142_checked fusedMap2142_checked
    DegreeOneSmallComparisons.comparison2142
#print axioms sourceMap2142_checked
#print axioms fusedMap2142_checked
#print axioms certified2142
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
