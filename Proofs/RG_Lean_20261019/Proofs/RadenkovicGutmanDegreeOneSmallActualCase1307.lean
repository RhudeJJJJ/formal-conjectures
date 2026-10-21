/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons26
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1307 : Family 9 := level9.get ⟨72,by decide⟩
def sourceMap1307 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![2,1,0,6,7,8,9,10,11,5,3,4] (sourceLabel 9 0 0 v)
def fusedMap1307 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![8,7,0,1,2,3,4,5,6,11,9,10] (fusedLabel 9 0 0 v)
theorem sourceMap1307_checked : acceptsGraphIso
    (source (graph core1307) (root 9) 0 0) DegreeOneSmallSpectrum450.graph sourceMap1307=true := by decide +kernel
theorem fusedMap1307_checked : acceptsGraphIso
    (fused (graph core1307) (root 9) 0 0) DegreeOneSmallSpectrum517.graph fusedMap1307=true := by decide +kernel
theorem certified1307 : Certified (graph core1307) (root 9) 0 0 :=
  of_native_maps core1307 DegreeOneSmallSpectrum450.graph DegreeOneSmallSpectrum517.graph
    sourceMap1307 fusedMap1307 sourceMap1307_checked fusedMap1307_checked
    DegreeOneSmallComparisons.comparison1307
#print axioms sourceMap1307_checked
#print axioms fusedMap1307_checked
#print axioms certified1307
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
