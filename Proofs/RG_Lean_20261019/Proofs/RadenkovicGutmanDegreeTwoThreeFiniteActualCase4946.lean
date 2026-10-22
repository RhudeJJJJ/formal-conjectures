/- Copyright 2026 Jonas J. Gebendorfer. Apache 2.0. -/
import Proofs.RadenkovicGutmanFiniteTreeNative
import Proofs.RadenkovicGutmanRootedCatalogueData
import Proofs.RadenkovicGutmanDegreeTwoThreeFiniteComparisons98
namespace Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
open RootedTreeEnumeration RootedCatalogueData FiniteTreeTransfer CoreQuotient
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def core4946 : Family 10 := level10.get ⟨1475,by decide⟩
def sourceMap4946 : (Vertices 10 ⊕ Fin 3 ⊕ Fin 3) → Fin 17 :=
  fun v => ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16] (sourceLabel 10 2 2 v)
def fusedMap4946 : (Vertices 10 ⊕ Fin 6) → Fin 17 :=
  fun v => ![1,2,3,4,5,6,7,8,9,10,11,0,12,13,14,15,16] (fusedLabel 10 2 2 v)
theorem sourceMap4946_checked : acceptsGraphIso
    (source (graph core4946) (root 10) 2 2) DegreeTwoThreeSpectrum7559.graph sourceMap4946=true := by decide +kernel
theorem fusedMap4946_checked : acceptsGraphIso
    (fused (graph core4946) (root 10) 2 2) DegreeTwoThreeSpectrum6961.graph fusedMap4946=true := by decide +kernel
theorem certified4946 : Certified (graph core4946) (root 10) 2 2 :=
  of_native_maps core4946 DegreeTwoThreeSpectrum7559.graph DegreeTwoThreeSpectrum6961.graph
    sourceMap4946 fusedMap4946 sourceMap4946_checked fusedMap4946_checked
    DegreeTwoThreeFiniteComparisons.comparison4946
#print axioms sourceMap4946_checked
#print axioms fusedMap4946_checked
#print axioms certified4946
end Gebendorfer.RadenkovicGutman.DegreeTwoThreeFiniteActualCases
