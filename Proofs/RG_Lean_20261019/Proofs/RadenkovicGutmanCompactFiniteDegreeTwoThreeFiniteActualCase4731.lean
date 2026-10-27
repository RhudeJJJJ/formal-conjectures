/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4731 : Family 10 := level10.get ⟨955,by decide⟩
def sourceMap4731 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![1,0,11,12,13,14,15,16,8,9,10,2,3,4,5,6,7] (sourceLabel 10 2 2 v)
def fusedMap4731 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4731_checked : acceptsGraphIso
    (source (graph core4731) (root 10) 2 2) DegreeTwoThreeSpectrum7498.graph sourceMap4731=true := by decide +kernel
theorem fusedMap4731_checked : acceptsGraphIso
    (fused (graph core4731) (root 10) 2 2) DegreeTwoThreeSpectrum5858.graph fusedMap4731=true := by decide +kernel
theorem certified4731 : Certified (graph core4731) (root 10) 2 2 :=
  of_native_maps core4731 DegreeTwoThreeSpectrum7498.graph DegreeTwoThreeSpectrum5858.graph
    sourceMap4731 fusedMap4731 sourceMap4731_checked fusedMap4731_checked
    DegreeTwoThreeFiniteComparisons.comparison4731
#print axioms sourceMap4731_checked
#print axioms fusedMap4731_checked
#print axioms certified4731
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
