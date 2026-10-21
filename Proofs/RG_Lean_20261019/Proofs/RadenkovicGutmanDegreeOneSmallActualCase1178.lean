/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeOneSmallComparisons23
namespace Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core1178 : Family 8 := level8.get ⟨214,by decide⟩
def sourceMap1178 : (Vertices 8 ⊕ Fin 2 ⊕ Fin 2) → Fin 13 :=
  fun v => ![8,0,1,2,3,4,5,6,7,9,10,11,12] (sourceLabel 8 1 1 v)
def fusedMap1178 : (Vertices 8 ⊕ Fin 4) → Fin 13 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12] (fusedLabel 8 1 1 v)
theorem sourceMap1178_checked : acceptsGraphIso
    (source (graph core1178) (root 8) 1 1) DegreeOneSmallSpectrum1780.graph sourceMap1178=true := by decide +kernel
theorem fusedMap1178_checked : acceptsGraphIso
    (fused (graph core1178) (root 8) 1 1) DegreeOneSmallSpectrum1113.graph fusedMap1178=true := by decide +kernel
theorem certified1178 : Certified (graph core1178) (root 8) 1 1 :=
  of_native_maps core1178 DegreeOneSmallSpectrum1780.graph DegreeOneSmallSpectrum1113.graph
    sourceMap1178 fusedMap1178 sourceMap1178_checked fusedMap1178_checked
    DegreeOneSmallComparisons.comparison1178
#print axioms sourceMap1178_checked
#print axioms fusedMap1178_checked
#print axioms certified1178
end Gebendorfer.RadenkovicGutman.DegreeOneSmallActualCases
