/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons85
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4274 : Family 9 := level9.get ⟨283,by decide⟩
def sourceMap4274 : (Vertices 9 ⊕ Fin 3 ⊕ Fin 3) → Fin 16 :=
  fun v => ![1,0,11,12,13,14,15,2,3,4,5,6,7,8,9,10] (sourceLabel 9 2 2 v)
def fusedMap4274 : (Vertices 9 ⊕ Fin 6) → Fin 16 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15] (fusedLabel 9 2 2 v)
theorem sourceMap4274_checked : acceptsGraphIso
    (source (graph core4274) (root 9) 2 2) DegreeTwoThreeSpectrum4864.graph sourceMap4274=true := by decide +kernel
theorem fusedMap4274_checked : acceptsGraphIso
    (fused (graph core4274) (root 9) 2 2) DegreeTwoThreeSpectrum4104.graph fusedMap4274=true := by decide +kernel
theorem certified4274 : Certified (graph core4274) (root 9) 2 2 :=
  of_native_maps core4274 DegreeTwoThreeSpectrum4864.graph DegreeTwoThreeSpectrum4104.graph
    sourceMap4274 fusedMap4274 sourceMap4274_checked fusedMap4274_checked
    DegreeTwoThreeFiniteComparisons.comparison4274
#print axioms sourceMap4274_checked
#print axioms fusedMap4274_checked
#print axioms certified4274
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
