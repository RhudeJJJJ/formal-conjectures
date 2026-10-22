/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons95
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4750 : Family 10 := level10.get ⟨1002,by decide⟩
def sourceMap4750 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4750 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4750_checked : acceptsGraphIso
    (source (graph core4750) (root 10) 2 2) DegreeTwoThreeSpectrum7075.graph sourceMap4750=true := by decide +kernel
theorem fusedMap4750_checked : acceptsGraphIso
    (fused (graph core4750) (root 10) 2 2) DegreeTwoThreeSpectrum5981.graph fusedMap4750=true := by decide +kernel
theorem certified4750 : Certified (graph core4750) (root 10) 2 2 :=
  of_native_maps core4750 DegreeTwoThreeSpectrum7075.graph DegreeTwoThreeSpectrum5981.graph
    sourceMap4750 fusedMap4750 sourceMap4750_checked fusedMap4750_checked
    DegreeTwoThreeFiniteComparisons.comparison4750
#print axioms sourceMap4750_checked
#print axioms fusedMap4750_checked
#print axioms certified4750
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
