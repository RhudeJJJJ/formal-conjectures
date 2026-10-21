/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons38
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1925 : Family 10 := level10.get ⟨217,by decide⟩
def sourceMap1925 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![10,9,8,0,1,2,3,4,5,6,7,11,12] (sourceLabel 10 0 0 v)
def fusedMap1925 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![10,9,0,1,2,3,4,5,6,7,8,11,12] (fusedLabel 10 0 0 v)
theorem sourceMap1925_checked : acceptsGraphIso
    (source (graph core1925) (root 10) 0 0) DegreeOneSmallSpectrum1098.graph sourceMap1925=true := by decide +kernel
theorem fusedMap1925_checked : acceptsGraphIso
    (fused (graph core1925) (root 10) 0 0) DegreeOneSmallSpectrum1101.graph fusedMap1925=true := by decide +kernel
theorem certified1925 : Certified (graph core1925) (root 10) 0 0 :=
  of_native_maps core1925 DegreeOneSmallSpectrum1098.graph DegreeOneSmallSpectrum1101.graph
    sourceMap1925 fusedMap1925 sourceMap1925_checked fusedMap1925_checked
    DegreeOneSmallComparisons.comparison1925
#print axioms sourceMap1925_checked
#print axioms fusedMap1925_checked
#print axioms certified1925
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
