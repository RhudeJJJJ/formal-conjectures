/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4129 : Family 8 := level8.get ⟨117,by decide⟩
def sourceMap4129 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![7,0,1,2,3,4,5,6,14,8,9,10,11,12,13] (sourceLabel 8 2 2 v)
def fusedMap4129 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4129_checked : acceptsGraphIso
    (source (graph core4129) (root 8) 2 2) DegreeTwoThreeSpectrum3259.graph sourceMap4129=true := by decide +kernel
theorem fusedMap4129_checked : acceptsGraphIso
    (fused (graph core4129) (root 8) 2 2) DegreeTwoThreeSpectrum2541.graph fusedMap4129=true := by decide +kernel
theorem certified4129 : Certified (graph core4129) (root 8) 2 2 :=
  of_native_maps core4129 DegreeTwoThreeSpectrum3259.graph DegreeTwoThreeSpectrum2541.graph
    sourceMap4129 fusedMap4129 sourceMap4129_checked fusedMap4129_checked
    DegreeTwoThreeFiniteComparisons.comparison4129
#print axioms sourceMap4129_checked
#print axioms fusedMap4129_checked
#print axioms certified4129
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
