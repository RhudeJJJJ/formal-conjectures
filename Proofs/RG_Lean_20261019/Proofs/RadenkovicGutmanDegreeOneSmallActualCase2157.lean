/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons43
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core2157 : Family 10 := level10.get ⟨620,by decide⟩
def sourceMap2157 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![2,1,0,5,6,7,8,9,10,11,12,3,4] (sourceLabel 10 0 0 v)
def fusedMap2157 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap2157_checked : acceptsGraphIso
    (source (graph core2157) (root 10) 0 0) DegreeOneSmallSpectrum1842.graph sourceMap2157=true := by decide +kernel
theorem fusedMap2157_checked : acceptsGraphIso
    (fused (graph core2157) (root 10) 0 0) DegreeOneSmallSpectrum1190.graph fusedMap2157=true := by decide +kernel
theorem certified2157 : Certified (graph core2157) (root 10) 0 0 :=
  of_native_maps core2157 DegreeOneSmallSpectrum1842.graph DegreeOneSmallSpectrum1190.graph
    sourceMap2157 fusedMap2157 sourceMap2157_checked fusedMap2157_checked
    DegreeOneSmallComparisons.comparison2157
#print axioms sourceMap2157_checked
#print axioms fusedMap2157_checked
#print axioms certified2157
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
