/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4108 : Family 8 := level8.get ⟨51,by decide⟩
def sourceMap4108 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![6,0,1,2,3,4,5,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4108 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4108_checked : acceptsGraphIso
    (source (graph core4108) (root 8) 2 2) DegreeTwoThreeSpectrum3358.graph sourceMap4108=true := by decide +kernel
theorem fusedMap4108_checked : acceptsGraphIso
    (fused (graph core4108) (root 8) 2 2) DegreeTwoThreeSpectrum2339.graph fusedMap4108=true := by decide +kernel
theorem certified4108 : Certified (graph core4108) (root 8) 2 2 :=
  of_native_maps core4108 DegreeTwoThreeSpectrum3358.graph DegreeTwoThreeSpectrum2339.graph
    sourceMap4108 fusedMap4108 sourceMap4108_checked fusedMap4108_checked
    DegreeTwoThreeFiniteComparisons.comparison4108
#print axioms sourceMap4108_checked
#print axioms fusedMap4108_checked
#print axioms certified4108
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
