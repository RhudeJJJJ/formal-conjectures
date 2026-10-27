/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons82
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4147 : Family 8 := level8.get ⟨162,by decide⟩
def sourceMap4147 : (Vertices 8 ⊕ Fin 3 ⊕ Fin 3) → Fin 15 :=
  fun v => ![0,8,9,10,11,12,13,14,7,1,2,3,4,5,6] (sourceLabel 8 2 2 v)
def fusedMap4147 : (Vertices 8 ⊕ Fin 6) → Fin 15 :=
  fun v => ![1,2,3,4,5,6,7,8,9,0,10,11,12,13,14] (fusedLabel 8 2 2 v)
theorem sourceMap4147_checked : acceptsGraphIso
    (source (graph core4147) (root 8) 2 2) DegreeTwoThreeSpectrum3621.graph sourceMap4147=true := by decide +kernel
theorem fusedMap4147_checked : acceptsGraphIso
    (fused (graph core4147) (root 8) 2 2) DegreeTwoThreeSpectrum2822.graph fusedMap4147=true := by decide +kernel
theorem certified4147 : Certified (graph core4147) (root 8) 2 2 :=
  of_native_maps core4147 DegreeTwoThreeSpectrum3621.graph DegreeTwoThreeSpectrum2822.graph
    sourceMap4147 fusedMap4147 sourceMap4147_checked fusedMap4147_checked
    DegreeTwoThreeFiniteComparisons.comparison4147
#print axioms sourceMap4147_checked
#print axioms fusedMap4147_checked
#print axioms certified4147
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
