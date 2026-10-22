/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4579 : Family 10 := level10.get ⟨538,by decide⟩
def sourceMap4579 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4579 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4579_checked : acceptsGraphIso
    (source (graph core4579) (root 10) 2 2) DegreeTwoThreeSpectrum7157.graph sourceMap4579=true := by decide +kernel
theorem fusedMap4579_checked : acceptsGraphIso
    (fused (graph core4579) (root 10) 2 2) DegreeTwoThreeSpectrum5187.graph fusedMap4579=true := by decide +kernel
theorem certified4579 : Certified (graph core4579) (root 10) 2 2 :=
  of_native_maps core4579 DegreeTwoThreeSpectrum7157.graph DegreeTwoThreeSpectrum5187.graph
    sourceMap4579 fusedMap4579 sourceMap4579_checked fusedMap4579_checked
    DegreeTwoThreeFiniteComparisons.comparison4579
#print axioms sourceMap4579_checked
#print axioms fusedMap4579_checked
#print axioms certified4579
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
