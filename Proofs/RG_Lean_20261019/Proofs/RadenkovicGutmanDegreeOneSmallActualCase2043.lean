/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons40
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2043 : Family 10 := level10.get ⟨404,by decide⟩
def sourceMap2043 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,8,9,10,11,12,5,6,7,3,4] (sourceLabel 10 0 0 v)
def fusedMap2043 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![7,6,0,1,2,3,4,5,10,11,12,8,9] (fusedLabel 10 0 0 v)
theorem sourceMap2043_checked : acceptsGraphIso
    (source (graph core2043) (root 10) 0 0) DegreeOneSmallSpectrum1194.graph sourceMap2043=true := by decide +kernel
theorem fusedMap2043_checked : acceptsGraphIso
    (fused (graph core2043) (root 10) 0 0) DegreeOneSmallSpectrum1505.graph fusedMap2043=true := by decide +kernel
theorem certified2043 : Certified (graph core2043) (root 10) 0 0 :=
  of_native_maps core2043 DegreeOneSmallSpectrum1194.graph DegreeOneSmallSpectrum1505.graph
    sourceMap2043 fusedMap2043 sourceMap2043_checked fusedMap2043_checked
    DegreeOneSmallComparisons.comparison2043
#print axioms sourceMap2043_checked
#print axioms fusedMap2043_checked
#print axioms certified2043
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
