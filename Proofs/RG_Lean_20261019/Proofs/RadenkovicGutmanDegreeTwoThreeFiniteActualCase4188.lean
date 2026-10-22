/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons83
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4188 : Family 8 := level8.get ⟨257,by decide⟩
def sourceMap4188 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,1,2,3,10,11,12,13,14,4,5,6,7,8,9] (sourceLabel 8 2 2 v)
def fusedMap4188 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4188_checked : acceptsGraphIso
    (source (graph core4188) (root 8) 2 2) DegreeTwoThreeSpectrum3849.graph sourceMap4188=true := by decide +kernel
theorem fusedMap4188_checked : acceptsGraphIso
    (fused (graph core4188) (root 8) 2 2) DegreeTwoThreeSpectrum2826.graph fusedMap4188=true := by decide +kernel
theorem certified4188 : Certified (graph core4188) (root 8) 2 2 :=
  of_native_maps core4188 DegreeTwoThreeSpectrum3849.graph DegreeTwoThreeSpectrum2826.graph
    sourceMap4188 fusedMap4188 sourceMap4188_checked fusedMap4188_checked
    DegreeTwoThreeFiniteComparisons.comparison4188
#print axioms sourceMap4188_checked
#print axioms fusedMap4188_checked
#print axioms certified4188
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
