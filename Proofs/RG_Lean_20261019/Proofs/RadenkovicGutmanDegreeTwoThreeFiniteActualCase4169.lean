/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4169 : Family 8 := level8.get ⟨212,by decide⟩
def sourceMap4169 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,4,5,6,13,14,7,8,9,10,11,12] (sourceLabel 8 2 2 v)
def fusedMap4169 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4169_checked : acceptsGraphIso
    (source (graph core4169) (root 8) 2 2) DegreeTwoThreeSpectrum3796.graph sourceMap4169=true := by decide +kernel
theorem fusedMap4169_checked : acceptsGraphIso
    (fused (graph core4169) (root 8) 2 2) DegreeTwoThreeSpectrum2510.graph fusedMap4169=true := by decide +kernel
theorem certified4169 : Certified (graph core4169) (root 8) 2 2 :=
  of_native_maps core4169 DegreeTwoThreeSpectrum3796.graph DegreeTwoThreeSpectrum2510.graph
    sourceMap4169 fusedMap4169 sourceMap4169_checked fusedMap4169_checked
    DegreeTwoThreeFiniteComparisons.comparison4169
#print axioms sourceMap4169_checked
#print axioms fusedMap4169_checked
#print axioms certified4169
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
