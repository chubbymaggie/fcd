import pefile
import bisect

stubs = {}
sectionStart = []
sectionInfo = {}

################################################################################
# fcd interface below
################################################################################

executableType = "Portable Executable"
targetTriple = "unknown-unknown-win32"
entryPoints = []

def init(data):
	global stubs
	global sectionStart
	global sectionInfo
	global entryPoints
	global targetTriple

	pe = pefile.PE(data=data)
	machineType = pefile.MACHINE_TYPE[pe.FILE_HEADER.Machine]
	if machineType == "IMAGE_FILE_MACHINE_I386":
		targetTriple = "x86-unknown-win32"
	elif machineType == "IMAGE_FILE_MACHINE_AMD64":
		targetTriple = "x86_64-unknown-win32"
	elif machineType == "IMAGE_FILE_MACHINE_ARM":
		targetTriple = "arm-unknown-win32"
	
	imageBase = pe.OPTIONAL_HEADER.ImageBase
	for section in pe.sections:
		virtualAddress = imageBase + section.VirtualAddress
		bisect.insort(sectionStart, virtualAddress)
		sectionInfo[virtualAddress] = (section.PointerToRawData, section.SizeOfRawData)
	
	for entry in pe.DIRECTORY_ENTRY_IMPORT:
		for imp in entry.imports:
			if imp.name:
				stubs[imp.address] = (entry.dll, imp.name)
			else:
				# make up some name based on the ordinal
				stubs[imp.address] = (entry.dll, "%s:%i" % (entry.dll, imp.ordinal))
	
	entry = (imageBase + pe.OPTIONAL_HEADER.AddressOfEntryPoint, "pe.start")
	entryPoints.append(entry)
	
	if hasattr(pe, "DIRECTORY_ENTRY_EXPORT"):
		for export in pe.DIRECTORY_ENTRY_EXPORT.symbols:
			exportTuple = (imageBase + export.address, export.name)
			entryPoints.append(exportTuple)

def getStubTarget(target):
	if target in stubs:
		return stubs[target]
	return None

def mapAddress(address):
	sectionIndex = bisect.bisect_right(sectionStart, address)
	if sectionIndex:
		sectionMaybeStart = sectionStart[sectionIndex-1]
		thisSectionInfo = sectionInfo[sectionMaybeStart]
		pointerOffset = address - sectionMaybeStart
		if pointerOffset <= thisSectionInfo[1]:
			return thisSectionInfo[0] + pointerOffset
	return None
