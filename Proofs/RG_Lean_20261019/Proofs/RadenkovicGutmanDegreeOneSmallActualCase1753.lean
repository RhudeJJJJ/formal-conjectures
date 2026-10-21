/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons35
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1753 : Family 9 := level9.get ⟨592,by decide⟩
def sourceMap1753 : (Vertices 9 ⊕ Fin 1 ⊕ Fin 1) → Fin 12 :=
  fun v => ![1,0,4,5,6,7,8,9,10,11,2,3] (sourceLabel 9 0 0 v)
def fusedMap1753 : (Vertices 9 ⊕ Fin 2) → Fin 12 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,10,11] (fusedLabel 9 0 0 v)
theorem sourceMap1753_checked : acceptsGraphIso
    (source (graph core1753) (root 9) 0 0) SmallGeFourSpectrum223.graph sourceMap1753=true := by decide +kernel
theorem fusedMap1753_checked : acceptsGraphIso
    (fused (graph core1753) (root 9) 0 0) SmallGeFourSpectrum141.graph fusedMap1753=true := by decide +kernel
theorem certified1753 : Certified (graph core1753) (root 9) 0 0 :=
  of_native_maps core1753 SmallGeFourSpectrum223.graph SmallGeFourSpectrum141.graph
    sourceMap1753 fusedMap1753 sourceMap1753_checked fusedMap1753_checked
    DegreeOneSmallComparisons.comparison1753
#print axioms sourceMap1753_checked
#print axioms fusedMap1753_checked
#print axioms certified1753
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
