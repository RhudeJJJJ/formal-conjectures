/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons91
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4598 : Family 10 := level10.get ⟨597,by decide⟩
def sourceMap4598 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![9,0,1,2,3,4,5,6,7,8,16,10,11,12,13,14,15] (sourceLabel 10 2 2 v)
def fusedMap4598 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4598_checked : acceptsGraphIso
    (source (graph core4598) (root 10) 2 2) DegreeTwoThreeSpectrum7244.graph sourceMap4598=true := by decide +kernel
theorem fusedMap4598_checked : acceptsGraphIso
    (fused (graph core4598) (root 10) 2 2) DegreeTwoThreeSpectrum5271.graph fusedMap4598=true := by decide +kernel
theorem certified4598 : Certified (graph core4598) (root 10) 2 2 :=
  of_native_maps core4598 DegreeTwoThreeSpectrum7244.graph DegreeTwoThreeSpectrum5271.graph
    sourceMap4598 fusedMap4598 sourceMap4598_checked fusedMap4598_checked
    DegreeTwoThreeFiniteComparisons.comparison4598
#print axioms sourceMap4598_checked
#print axioms fusedMap4598_checked
#print axioms certified4598
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
