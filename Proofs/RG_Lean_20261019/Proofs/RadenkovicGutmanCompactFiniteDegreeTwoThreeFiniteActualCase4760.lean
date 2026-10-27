/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4760 : Family 10 := level10.get ⟨1028,by decide⟩
def sourceMap4760 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![7,0,1,2,3,4,5,6,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4760 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4760_checked : acceptsGraphIso
    (source (graph core4760) (root 10) 2 2) DegreeTwoThreeSpectrum7105.graph sourceMap4760=true := by decide +kernel
theorem fusedMap4760_checked : acceptsGraphIso
    (fused (graph core4760) (root 10) 2 2) DegreeTwoThreeSpectrum6038.graph fusedMap4760=true := by decide +kernel
theorem certified4760 : Certified (graph core4760) (root 10) 2 2 :=
  of_native_maps core4760 DegreeTwoThreeSpectrum7105.graph DegreeTwoThreeSpectrum6038.graph
    sourceMap4760 fusedMap4760 sourceMap4760_checked fusedMap4760_checked
    DegreeTwoThreeFiniteComparisons.comparison4760
#print axioms sourceMap4760_checked
#print axioms fusedMap4760_checked
#print axioms certified4760
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
