/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons36
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1814 : Family 10 := level10.get ⟨57,by decide⟩
def sourceMap1814 : (Vertices 10 ⊕ Fin 1 ⊕ Fin 1) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (sourceLabel 10 0 0 v)
def fusedMap1814 : (Vertices 10 ⊕ Fin 2) → Fin 13 :=
  fun v => ![9,8,7,0,1,2,3,4,5,6,12,10,11] (fusedLabel 10 0 0 v)
theorem sourceMap1814_checked : acceptsGraphIso
    (source (graph core1814) (root 10) 0 0) DegreeOneSmallSpectrum1066.graph sourceMap1814=true := by decide +kernel
theorem fusedMap1814_checked : acceptsGraphIso
    (fused (graph core1814) (root 10) 0 0) DegreeOneSmallSpectrum869.graph fusedMap1814=true := by decide +kernel
theorem certified1814 : Certified (graph core1814) (root 10) 0 0 :=
  of_native_maps core1814 DegreeOneSmallSpectrum1066.graph DegreeOneSmallSpectrum869.graph
    sourceMap1814 fusedMap1814 sourceMap1814_checked fusedMap1814_checked
    DegreeOneSmallComparisons.comparison1814
#print axioms sourceMap1814_checked
#print axioms fusedMap1814_checked
#print axioms certified1814
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
