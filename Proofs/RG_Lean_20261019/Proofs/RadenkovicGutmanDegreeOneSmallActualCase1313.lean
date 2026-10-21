/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1313 : Family 9 := level9.get ⟨76,by decide⟩
def sourceMap1313 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1313 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1313_checked : acceptsGraphIso
    (source (graph core1313) (root 9) 0 0) DegreeOneSmallSpectrum473.graph sourceMap1313=true := by decide +kernel
theorem fusedMap1313_checked : acceptsGraphIso
    (fused (graph core1313) (root 9) 0 0) DegreeOneSmallSpectrum534.graph fusedMap1313=true := by decide +kernel
theorem certified1313 : Certified (graph core1313) (root 9) 0 0 :=
  of_native_maps core1313 DegreeOneSmallSpectrum473.graph DegreeOneSmallSpectrum534.graph
    sourceMap1313 fusedMap1313 sourceMap1313_checked fusedMap1313_checked
    DegreeOneSmallComparisons.comparison1313
#print axioms sourceMap1313_checked
#print axioms fusedMap1313_checked
#print axioms certified1313
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
