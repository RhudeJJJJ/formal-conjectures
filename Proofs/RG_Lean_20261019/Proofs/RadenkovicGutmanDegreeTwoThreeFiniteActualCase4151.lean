/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4151 : Family 8 := level8.get ⟨172,by decide⟩
def sourceMap4151 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4151 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4151_checked : acceptsGraphIso
    (source (graph core4151) (root 8) 2 2) DegreeTwoThreeSpectrum3625.graph sourceMap4151=true := by decide +kernel
theorem fusedMap4151_checked : acceptsGraphIso
    (fused (graph core4151) (root 8) 2 2) DegreeTwoThreeSpectrum2875.graph fusedMap4151=true := by decide +kernel
theorem certified4151 : Certified (graph core4151) (root 8) 2 2 :=
  of_native_maps core4151 DegreeTwoThreeSpectrum3625.graph DegreeTwoThreeSpectrum2875.graph
    sourceMap4151 fusedMap4151 sourceMap4151_checked fusedMap4151_checked
    DegreeTwoThreeFiniteComparisons.comparison4151
#print axioms sourceMap4151_checked
#print axioms fusedMap4151_checked
#print axioms certified4151
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
