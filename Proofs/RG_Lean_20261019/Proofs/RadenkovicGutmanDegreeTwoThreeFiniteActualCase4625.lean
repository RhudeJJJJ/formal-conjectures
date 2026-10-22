/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons92
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4625 : Family 10 := level10.get ⟨670,by decide⟩
def sourceMap4625 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![6,0,1,2,3,4,5,16,7,8,9,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4625 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4625_checked : acceptsGraphIso
    (source (graph core4625) (root 10) 2 2) DegreeTwoThreeSpectrum7311.graph sourceMap4625=true := by decide +kernel
theorem fusedMap4625_checked : acceptsGraphIso
    (fused (graph core4625) (root 10) 2 2) DegreeTwoThreeSpectrum5385.graph fusedMap4625=true := by decide +kernel
theorem certified4625 : Certified (graph core4625) (root 10) 2 2 :=
  of_native_maps core4625 DegreeTwoThreeSpectrum7311.graph DegreeTwoThreeSpectrum5385.graph
    sourceMap4625 fusedMap4625 sourceMap4625_checked fusedMap4625_checked
    DegreeTwoThreeFiniteComparisons.comparison4625
#print axioms sourceMap4625_checked
#print axioms fusedMap4625_checked
#print axioms certified4625
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
