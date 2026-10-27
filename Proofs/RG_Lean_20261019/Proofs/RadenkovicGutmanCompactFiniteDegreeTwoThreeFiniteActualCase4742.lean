/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanCompactFiniteDegreeTwoThreeFiniteComparisons94
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4742 : Family 10 := level10.get ⟨977,by decide⟩
def sourceMap4742 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,12,13,14,15,16,1,2,3,4,5,6,7,8,9,10,11] (sourceLabel 10 2 2 v)
def fusedMap4742 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4742_checked : acceptsGraphIso
    (source (graph core4742) (root 10) 2 2) DegreeTwoThreeSpectrum6762.graph sourceMap4742=true := by decide +kernel
theorem fusedMap4742_checked : acceptsGraphIso
    (fused (graph core4742) (root 10) 2 2) DegreeTwoThreeSpectrum5911.graph fusedMap4742=true := by decide +kernel
theorem certified4742 : Certified (graph core4742) (root 10) 2 2 :=
  of_native_maps core4742 DegreeTwoThreeSpectrum6762.graph DegreeTwoThreeSpectrum5911.graph
    sourceMap4742 fusedMap4742 sourceMap4742_checked fusedMap4742_checked
    DegreeTwoThreeFiniteComparisons.comparison4742
#print axioms sourceMap4742_checked
#print axioms fusedMap4742_checked
#print axioms certified4742
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
